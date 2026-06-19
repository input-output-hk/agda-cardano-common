{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Single-channel refinement of the Cardano `Network` against `CopySpec`.
--
-- Instance `p1`: numConns N2N_KeepAlive = 1, every other protocol = 0;
-- all abstract data domains and the forwarded payload `Data` are `⊤`.
-- Then the five non-KeepAlive protocols collapse to `⦀Fin 0 = Skip` and
-- KeepAlive has the single connection `c0 = fzero`, so `Network`/`CopySpec`
-- reduce (modulo the `⦀ Skip` cruft + the `Par⊤`/`∖` stack) to the single
-- channel `(KeepAlive, c0)` pipeline vs `Copy KeepAlive c0`.
--
-- MAIN RESULT (proved below, postulate-free / no holes):
--   `CopySpec⊑D-Network : CopySpec ⊑D Network`
-- — the divergence-refinement: `Network` has NO divergences along any trace,
-- so the inclusion `divergences Network ⊆ divergences CopySpec` is vacuous.
--
-- HOW.  `divergences Network s` carries a weakly-reachable witness `W` with
-- `Diverges W`; `Reach-noDiv` rules every such `W` out GIVEN the coinductive
-- invariant `GoodU (Par⊤ csTA' TxSide RxSide)`.  That invariant is supplied
-- by a verified FINITE-STATE ABSTRACTION of the un-hidden composite:
--   * `CSP.Examples.Cardano_network.NetModel` — an abstract control-state
--     automaton `CS` (six per-leaf position enums) with internal `_⇒ᵢ_` and
--     visible `_⇒ᵥ_` transitions, and a measure `μ` that EVERY `_⇒ᵢ_` step
--     strictly decreases (`μ-dec`).  The loop-restart "guard" diamonds are
--     absorbed uniformly by `μ` (every internal step drops it by one);
--   * a decode `⟦_⟧ : CS → NetProc` matching the concrete composite by `refl`
--     (`dec-cs0 : ⟦ cs0 ⟧ ≡ T`, and `dec-U0 … dec-U8`);
--   * a compositional simulation `sim-modA` / `sim-uVis` — every concrete
--     `ModAStep` / non-csTA visible step of `⟦ cs ⟧` maps to a `_⇒ᵢ_` / `_⇒ᵥ_`
--     with definitionally-matching target — glued from per-leaf step
--     characterizations through the `Par`/`Hide` elimination lemmas;
--   * hence `MAcc-cs` (by `μ`-well-foundedness) ⇒ `goodU-cs` ⇒ `goodU-T0`.
-- `CopySpec` is τ-free ⇒ `¬ Diverges CopySpec` (the trivial divergence side).
--
-- The PHASE-A block (states `U0 … U8f` on the un-hidden composite, with the
-- definitional cycle closure `U8f ≡ U0`) is the concrete state walk that the
-- abstraction's decode is validated against.
--
-- NEXT (not done here): trace refinement (`⊑T` both ways) and the full
-- `Network ≈DR CopySpec` master key (whence `≈FD` via `drbisim→≈FD`); the
-- `CS`/decode/simulation backbone is directly reusable for that weak
-- simulation.
------------------------------------------------------------------------

open import Level using (0ℓ; lift)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Nat using (ℕ)
open import Data.Fin using (zero) renaming (suc to fs)
open import Data.Fin using () renaming (zero to fz)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Class.DecEq using (DecEq)

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using
  ( IDs; N2N_KeepAlive
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
  ; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetModel
  using ( CS; mkCS; cs0
        ; IP; I0; I1; I2; Ig
        ; TP; T0; T1; Tg
        ; RP; R0; R1; Rg
        ; OP; O0; O1; O2; Og
        ; CP; Rc0; Rc1; Rcg
        ; SP; Sa0; Sa1; Sag
        ; _⇒ᵢ_; _⇒ᵥ_
        ; gI; gT; gR; gO; gRc; gSa )
import CSP.Examples.Cardano_network.NetModel as NM

module CSP.Examples.Cardano_network.NetworkRefinement where

open PTree
open ExtI

------------------------------------------------------------------------
-- The single-channel instance.
------------------------------------------------------------------------

instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

p1 : Params
p1 = record
  { Cookie = ⊤ ; Block = ⊤ ; Txid = ⊤ ; LSlot = ⊤
  ; VoterId = ⊤ ; LFBitmap = ⊤ ; VoteBlob = ⊤
  ; numConns = λ where N2N_KeepAlive → 1 ; _ → 0
  ; decCookie  = decEq⊤ ; decBlock    = decEq⊤ ; decTxid    = decEq⊤
  ; decLSlot   = decEq⊤ ; decVoterId  = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤ }

open import CSP.Examples.Cardano_network.Net p1
  using (Net; Conn; input; output; sndmsg; tx)
open import CSP.Examples.Cardano_network.Network p1 ⊤

open import Semantics.LTS {E = Net ⊤} {I = ExtI (Net ⊤)}
open import Semantics.WeakBisim {E = Net ⊤} {I = ExtI (Net ⊤)}
open import Semantics.DRBisim {E = Net ⊤} {I = ExtI (Net ⊤)} using (Diverges; _≈DR_; deadlock-converges)
open import Semantics.Failures {E = Net ⊤} {I = ExtI (Net ⊤)}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.FailuresDivergences {E = Net ⊤} {I = ExtI (Net ⊤)}
  using (_⊑D_; divergences; IsDivergence)

-- the Net-decidable-equality used to instantiate every law module
open import CSP.Examples.Cardano_network.Net p1 using (Net-≟)

open import CSP.Operators {E = Net ⊤} (Net-≟ {⊤})
  using (Par⊤; _⦀_; _∖_; chanSet; ∅ES; EventSet; Skip)
open EventSet

⊤merge : Poly.⊤ {0ℓ} → Poly.⊤ {0ℓ} → Poly.⊤ {0ℓ}
⊤merge _ _ = Poly.tt

open import CSP.Laws.FD.HideDivergence (Net-≟ {⊤})
  using (MAcc; macc; Hide-noDiv-from-MAcc)
open import CSP.Laws.Bisim.DRCongruence (Net-≟ {⊤})
  using (ModAStep; maτ; maE; DivModA)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {⊤})
  using (Par-τ-elim; ParτR; τL; τR
        ; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Traces.TraceLawsHide (Net-≟ {⊤})
  using (Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net-≟ {⊤})
  using (deadlock-no-τ; deadlock-no-ev)

NetR : Set
NetR = Poly.⊤ {0ℓ}

c0 : Conn N2N_KeepAlive
c0 = zero

------------------------------------------------------------------------
-- State extractors: read the visible-offer continuation out of a node.
------------------------------------------------------------------------

vis-of : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR
       → (at : AnyTypes (Net ⊤)) → proj₁ at → Maybe NetProc
vis-of (react v _) = v
vis-of _           = λ _ _ → nothing

------------------------------------------------------------------------
-- N0 = Network.  Initial visible offer: `input`.
------------------------------------------------------------------------

inputAt : AnyTypes (Net ⊤)
inputAt = (⊤ , input N2N_KeepAlive c0)

inputLbl : Event√ NetR
inputLbl = evl (evLabel ⊤ (input N2N_KeepAlive c0) tt)

-- `input` IS offered initially (sanity-style).
offers-input : is-just (vis-of (force Network) inputAt tt) ≡ true
offers-input = refl

-- N1 := the input-successor of Network.
N1 : NetProc
N1 with vis-of (force Network) inputAt tt
... | just t  = t
... | nothing = Network

-- Network can fire `input` to N1 (force reduces; offer = just N1).
N0─input─►N1 : Network ─[ ev inputLbl ]─► N1
N0─input─►N1 = sVis {at = inputAt} refl refl

-- N1 does NOT yet offer `output` (it is mid-pipeline; must τ first).
N1-no-output : vis-of (force N1) (⊤ , output N2N_KeepAlive c0) tt ≡ nothing
N1-no-output = refl

------------------------------------------------------------------------
-- First hidden τ-step: N1 fires the hidden `sndmsg` (synchronised inside
-- TxSide's `Par⊤ csSR`, then hidden by csSR ⇒ τ; propagated unchanged
-- through the `Par⊤ csTA` and the outer Network hide).
--
-- The nested `ExtI`-index threads:
--   outer hide csTA  tag0 (P's own τ)         → pair fin _
--   inner Par⊤ csTA  tag0 (P=TxSide side)     → pair fin _
--   TxSide hide csSR tag1 (newly hidden evt)  → pair fin (base sndmsg)
-- with the inner sync of `sndmsg` between Inputs and Transmitter.
------------------------------------------------------------------------

sndmsgIdx : AnyTypes (ExtI (Net ⊤))
sndmsgIdx = _ , pair (fin {n = 2})
                 (pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (sndmsg N2N_KeepAlive c0))))

sndmsgVal : proj₁ sndmsgIdx
sndmsgVal = lift fz , (lift fz , (lift (fs fz) , tt))

-- N2 := the τ-successor of N1.
N2 : NetProc
N2 with (vis-of-τ (force N1))
  where
  vis-of-τ : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR → Maybe NetProc
  vis-of-τ (react _ τc) = τc sndmsgIdx sndmsgVal
  vis-of-τ _            = nothing
... | just t  = t
... | nothing = N1

N1─τ─►N2 : N1 ─[ τ ]─► N2
N1─τ─►N2 = sTau {i = sndmsgIdx} {a = sndmsgVal} refl refl

-- Second hidden τ-step: N2 fires `tx` (synchronised between TxSide and
-- RxSide in `Par⊤ csTA`, then hidden by csTA ⇒ τ); tag1 at the outer hide.
txIdx : AnyTypes (ExtI (Net ⊤))
txIdx = _ , pair (fin {n = 2}) (base (tx N2N_KeepAlive c0))

txVal : proj₁ txIdx
txVal = lift (fs fz) , tt

N3 : NetProc
N3 with (vis-of-τ (force N2))
  where
  vis-of-τ : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR → Maybe NetProc
  vis-of-τ (react _ τc) = τc txIdx txVal
  vis-of-τ _            = nothing
... | just t  = t
... | nothing = N2

N2─τ─►N3 : N2 ─[ τ ]─► N3
N2─τ─►N3 = sTau {i = txIdx} {a = txVal} refl refl

-- Third hidden τ-step: N3 fires `rcvmsg` (hidden in RxSide's csSR... csRS);
-- outer csTA tag0 (own τ), inner Par⊤ csTA tag1 (Q=RxSide), csRS tag1.
open import CSP.Examples.Cardano_network.Net p1 using (rcvmsg)

rcvmsgIdx : AnyTypes (ExtI (Net ⊤))
rcvmsgIdx = _ , pair (fin {n = 2})
                 (pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (rcvmsg N2N_KeepAlive c0))))

rcvmsgVal : proj₁ rcvmsgIdx
rcvmsgVal = lift fz , (lift (fs fz) , (lift (fs fz) , tt))

N4 : NetProc
N4 with (vis-of-τ (force N3))
  where
  vis-of-τ : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR → Maybe NetProc
  vis-of-τ (react _ τc) = τc rcvmsgIdx rcvmsgVal
  vis-of-τ _            = nothing
... | just t  = t
... | nothing = N3

N3─τ─►N4 : N3 ─[ τ ]─► N4
N3─τ─►N4 = sTau {i = rcvmsgIdx} {a = rcvmsgVal} refl refl

-- N4 now offers `output` (and no longer `input`).
outputAt : AnyTypes (Net ⊤)
outputAt = (⊤ , output N2N_KeepAlive c0)

outputLbl : Event√ NetR
outputLbl = evl (evLabel ⊤ (output N2N_KeepAlive c0) tt)

N4-offers-output : is-just (vis-of (force N4) outputAt tt) ≡ true
N4-offers-output = refl

N4-no-input : vis-of (force N4) inputAt tt ≡ nothing
N4-no-input = refl

-- N5 := the output-successor of N4.
N5 : NetProc
N5 with vis-of (force N4) outputAt tt
... | just t  = t
... | nothing = N4

N4─output─►N5 : N4 ─[ ev outputLbl ]─► N5
N4─output─►N5 = sVis {at = outputAt} refl refl

open import CSP.Examples.Cardano_network.Net p1 using (sndack; ack; rcvack)

-- N5 --sndack--> N6 (hidden in RxSide csRS; same shape as rcvmsg).
sndackIdx : AnyTypes (ExtI (Net ⊤))
sndackIdx = _ , pair (fin {n = 2})
                 (pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (sndack N2N_KeepAlive c0))))
sndackVal : proj₁ sndackIdx
sndackVal = lift fz , (lift (fs fz) , (lift (fs fz) , tt))

N6 : NetProc
N6 with (vis-of-τ (force N5))
  where
  vis-of-τ : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR → Maybe NetProc
  vis-of-τ (react _ τc) = τc sndackIdx sndackVal
  vis-of-τ _            = nothing
... | just t  = t
... | nothing = N5

N5─τ─►N6 : N5 ─[ τ ]─► N6
N5─τ─►N6 = sTau {i = sndackIdx} {a = sndackVal} refl refl

-- N6 --ack--> N7 (synchronised in csTA; tag1 at the outer hide, like tx).
ackIdx : AnyTypes (ExtI (Net ⊤))
ackIdx = _ , pair (fin {n = 2}) (base (ack N2N_KeepAlive c0))
ackVal : proj₁ ackIdx
ackVal = lift (fs fz) , tt

N7 : NetProc
N7 with (vis-of-τ (force N6))
  where
  vis-of-τ : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR → Maybe NetProc
  vis-of-τ (react _ τc) = τc ackIdx ackVal
  vis-of-τ _            = nothing
... | just t  = t
... | nothing = N6

N6─τ─►N7 : N6 ─[ τ ]─► N7
N6─τ─►N7 = sTau {i = ackIdx} {a = ackVal} refl refl

-- N7 --rcvack--> N8 (hidden in TxSide csSR; outer csTA tag0, Par tag0
-- (P=TxSide), csSR tag1, base rcvack — same shape as the sndmsg step).
rcvackIdx : AnyTypes (ExtI (Net ⊤))
rcvackIdx = _ , pair (fin {n = 2})
                 (pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (rcvack N2N_KeepAlive c0))))
rcvackVal : proj₁ rcvackIdx
rcvackVal = lift fz , (lift fz , (lift (fs fz) , tt))

N8 : NetProc
N8 with (vis-of-τ (force N7))
  where
  vis-of-τ : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR → Maybe NetProc
  vis-of-τ (react _ τc) = τc rcvackIdx rcvackVal
  vis-of-τ _            = nothing
... | just t  = t
... | nothing = N7

N7─τ─►N8 : N7 ─[ τ ]─► N8
N7─τ─►N8 = sTau {i = rcvackIdx} {a = rcvackVal} refl refl

-- N5, N6, N7 are genuine MID-(back-)PATH states: they offer NEITHER `input`
-- NOR `output` (the back-path sndack/ack/rcvack are all hidden ⇒ τ).  These
-- confirm the back-path τ-chain does not get stuck on a visible offer.
N5-mid-in  : vis-of (force N5) inputAt  tt ≡ nothing
N5-mid-in  = refl
N5-mid-out : vis-of (force N5) outputAt tt ≡ nothing
N5-mid-out = refl
N6-mid-in  : vis-of (force N6) inputAt  tt ≡ nothing
N6-mid-in  = refl
N6-mid-out : vis-of (force N6) outputAt tt ≡ nothing
N6-mid-out = refl
N7-mid-in  : vis-of (force N7) inputAt  tt ≡ nothing
N7-mid-in  = refl
N7-mid-out : vis-of (force N7) outputAt tt ≡ nothing
N7-mid-out = refl

-- NOTE: the cycle closure on the HIDDEN side (`N8 ≡ N0`) was not pursued
-- here; instead it is settled on the UN-HIDDEN composite `T` in the Phase A
-- block at the bottom of this file (`U8f ≡ U0`, by `refl`).  The original
-- `N8` "stuck mid-state" was NOT a wrong rcvack tag — rather the back-path
-- needs SIX `sil`-guard τ's (one per looped leaf: RcvAck, Transmitter,
-- Input, Output, Receiver, SndAck) before every leaf is reset to its
-- `loop0`-body form; landing on any one guard alone looks "stuck".

------------------------------------------------------------------------
-- The easy divergence side: CopySpec is τ-free, hence non-divergent.
--
-- `CopySpec` head is a stable `react` (its τ-branch map is everywhere
-- `nothing`), so it admits no τ-step at all; `Diverges` needs a first
-- τ-step, so it is uninhabited.
------------------------------------------------------------------------

-- CopySpec's head node offers no τ at the index/value used by any τ-step:
-- we refute `Diverges` by case-splitting its first `step`.
CopySpec-stable : ∀ {t} → CopySpec ─[ τ ]─► t → ⊥
CopySpec-stable (sSil ())
CopySpec-stable (sTau {i = _ , fin}                       refl ())
CopySpec-stable (sTau {i = _ , base _}                    refl ())
CopySpec-stable (sTau {i = _ , pair fin (base _)}         refl ())
CopySpec-stable (sTau {i = _ , pair fin fin}              refl ())
CopySpec-stable (sTau {i = _ , pair fin (pair _ _)}       refl ())
CopySpec-stable (sTau {i = _ , pair (base _) _}           refl ())
CopySpec-stable (sTau {i = _ , pair (pair _ _) _}         refl ())

¬Diverges-CopySpec : ¬ Diverges CopySpec
¬Diverges-CopySpec d = CopySpec-stable (d .Diverges.step)

------------------------------------------------------------------------
-- Weak reachability: N0 weakly reaches N4 by `input` (one visible step
-- padded by the three hidden τ's sndmsg/tx/rcvmsg).  This is exactly the
-- backward-simulation witness CopySpec's `input` would have to match.
------------------------------------------------------------------------

N0═input═►N4 : Network ═[ ev inputLbl ]═► N4
N0═input═►N4 =
  wev τ*-refl N0─input─►N1
      (τ*-step N1─τ─►N2 (τ*-step N2─τ─►N3 (τ*-step N3─τ─►N4 τ*-refl)))

------------------------------------------------------------------------
-- GOALS (the exploratory targets).  Stated here as the intended type
-- signatures; their proofs require the full DR-bisimulation core, which is
-- the documented open obstacle (see `.git/sdd/net-refine-report.md`):
--
--   net≈DR : Network ≈DR CopySpec
--   net≈FD : Network ≈FD CopySpec                       (= drbisim→≈FD net≈DR)
--   net⊑T  : Network ⊑T CopySpec                        (from drbisim→wbisim + traces-respects-≈)
--   spec⊑T : CopySpec ⊑T Network
--
-- The TRACE-equivalence corollary is derivable from `≈DR` WITHOUT the
-- failures bridge, via weak bisimulation:
--   open Semantics.DRBisim          using (drbisim→wbisim)
--   open Semantics.Failures         using (traces-respects-≈)
--   net⊑T  s qtr = proj₂ (traces-respects-≈ (drbisim→wbisim (drbisim-sym net≈DR))) qtr
--   spec⊑T s qtr = proj₂ (traces-respects-≈ (drbisim→wbisim net≈DR)) qtr
-- (recall `P ⊑T Q = ∀ s → traces Q s → traces P s`).

------------------------------------------------------------------------
-- MILESTONE 1: ¬ Diverges Network.
--
-- The single-channel `Network` is DEADLOCKED at its initial state: with
-- no `input` ever received, NO leaf can move.  Hence the top `Par`/`∖`
-- node is "modulo-csTA stable" (admits neither a τ nor a hidden tx/ack),
-- so it cannot begin an infinite modulo-csTA path ⇒ `¬ Diverges Network`
-- via the Hide-divergence König infrastructure (MAcc descent).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Net p1 using (output)

-- The eight raw τ-branch index shapes of a stable react head; every leaf
-- below has an everywhere-`nothing` τ-map, so each is refuted by `refl ()`.
Transmitter-stable : ∀ {t} → Transmitter ─[ τ ]─► t → ⊥
Transmitter-stable (sSil ())
Transmitter-stable (sTau {i = _ , fin}                 refl ())
Transmitter-stable (sTau {i = _ , base _}              refl ())
Transmitter-stable (sTau {i = _ , pair fin (base _)}   refl ())
Transmitter-stable (sTau {i = _ , pair fin fin}        refl ())
Transmitter-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
Transmitter-stable (sTau {i = _ , pair (base _) _}     refl ())
Transmitter-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

Receiver-stable : ∀ {t} → Receiver ─[ τ ]─► t → ⊥
Receiver-stable (sSil ())
Receiver-stable (sTau {i = _ , fin}                 refl ())
Receiver-stable (sTau {i = _ , base _}              refl ())
Receiver-stable (sTau {i = _ , pair fin (base _)}   refl ())
Receiver-stable (sTau {i = _ , pair fin fin}        refl ())
Receiver-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
Receiver-stable (sTau {i = _ , pair (base _) _}     refl ())
Receiver-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

SndAck-stable : ∀ {t} → SndAck ─[ τ ]─► t → ⊥
SndAck-stable (sSil ())
SndAck-stable (sTau {i = _ , fin}                 refl ())
SndAck-stable (sTau {i = _ , base _}              refl ())
SndAck-stable (sTau {i = _ , pair fin (base _)}   refl ())
SndAck-stable (sTau {i = _ , pair fin fin}        refl ())
SndAck-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
SndAck-stable (sTau {i = _ , pair (base _) _}     refl ())
SndAck-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

RcvAck-stable : ∀ {t} → RcvAck ─[ τ ]─► t → ⊥
RcvAck-stable (sSil ())
RcvAck-stable (sTau {i = _ , fin}                 refl ())
RcvAck-stable (sTau {i = _ , base _}              refl ())
RcvAck-stable (sTau {i = _ , pair fin (base _)}   refl ())
RcvAck-stable (sTau {i = _ , pair fin fin}        refl ())
RcvAck-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
RcvAck-stable (sTau {i = _ , pair (base _) _}     refl ())
RcvAck-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

Input-stable : ∀ {t} → Input N2N_KeepAlive c0 ─[ τ ]─► t → ⊥
Input-stable (sSil ())
Input-stable (sTau {i = _ , fin}                 refl ())
Input-stable (sTau {i = _ , base _}              refl ())
Input-stable (sTau {i = _ , pair fin (base _)}   refl ())
Input-stable (sTau {i = _ , pair fin fin}        refl ())
Input-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
Input-stable (sTau {i = _ , pair (base _) _}     refl ())
Input-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

Output-stable : ∀ {t} → Output N2N_KeepAlive c0 ─[ τ ]─► t → ⊥
Output-stable (sSil ())
Output-stable (sTau {i = _ , fin}                 refl ())
Output-stable (sTau {i = _ , base _}              refl ())
Output-stable (sTau {i = _ , pair fin (base _)}   refl ())
Output-stable (sTau {i = _ , pair fin fin}        refl ())
Output-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
Output-stable (sTau {i = _ , pair (base _) _}     refl ())
Output-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

-- Skip = ret tt: no τ.
Skip-stable : ∀ {t} → Skip {0ℓ} ─[ τ ]─► t → ⊥
Skip-stable (sSil ())
Skip-stable (sTau () _)

-- `Inputs`/`Outputs` reduce to a react whose τ-map is everywhere nothing
-- (the single live leaf is itself stable, interleaved with Skips): try the
-- raw 8-clause refutation.
Inputs-stable : ∀ {t} → Inputs ─[ τ ]─► t → ⊥
Inputs-stable (sSil ())
Inputs-stable (sTau {i = _ , fin}                 refl ())
Inputs-stable (sTau {i = _ , base _}              refl ())
Inputs-stable (sTau {i = _ , pair fin (base _)}   refl ())
Inputs-stable (sTau {i = _ , pair fin fin}        refl ())
Inputs-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
Inputs-stable (sTau {i = _ , pair (base _) _}     refl ())
Inputs-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

Outputs-stable : ∀ {t} → Outputs ─[ τ ]─► t → ⊥
Outputs-stable (sSil ())
Outputs-stable (sTau {i = _ , fin}                 refl ())
Outputs-stable (sTau {i = _ , base _}              refl ())
Outputs-stable (sTau {i = _ , pair fin (base _)}   refl ())
Outputs-stable (sTau {i = _ , pair fin fin}        refl ())
Outputs-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
Outputs-stable (sTau {i = _ , pair (base _) _}     refl ())
Outputs-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

-- TR = Transmitter ⦀ RcvAck is stable: a τ of the ⦀-Par is a τ of one side.
TR-stable : ∀ {t} → (Transmitter ⦀ RcvAck) ─[ τ ]─► t → ⊥
TR-stable step with Par-τ-elim ∅ES ⊤merge Transmitter RcvAck step
... | τL _ Pτ _ = Transmitter-stable Pτ
... | τR _ Qτ _ = RcvAck-stable Qτ

-- RS = Receiver ⦀ SndAck is stable.
RS-stable : ∀ {t} → (Receiver ⦀ SndAck) ─[ τ ]─► t → ⊥
RS-stable step with Par-τ-elim ∅ES ⊤merge Receiver SndAck step
... | τL _ Pτ _ = Receiver-stable Pτ
... | τR _ Qτ _ = SndAck-stable Qτ

------------------------------------------------------------------------
-- Non-offer lemmas: which hidden/sync events each operand REFUSES.
-- (`Inputs` only offers `input`; `Outputs` only offers `rcvmsg`→… i.e.
-- its sole visible offer is `rcvmsg`, but NOT `sndack`; the leaves below
-- list exactly the refusals the sync/hide eliminations demand.)
------------------------------------------------------------------------

-- Inputs refuses sndmsg and rcvack on ANY id/connection (it offers only `input`).
Inputs-no-sndmsg : ∀ {t a id} {c : Conn id} →
  Inputs ─[ ev (evl (evLabel ⊤ (sndmsg id c) a)) ]─► t → ⊥
Inputs-no-sndmsg (sVis refl ())

Inputs-no-rcvack : ∀ {t a id} {c : Conn id} →
  Inputs ─[ ev (evl (evLabel ⊤ (rcvack id c) a)) ]─► t → ⊥
Inputs-no-rcvack (sVis refl ())

-- Outputs refuses sndack on ANY id/connection (it offers only `rcvmsg`).
Outputs-no-sndack : ∀ {t a id} {c : Conn id} →
  Outputs ─[ ev (evl (evLabel ⊤ (sndack id c) a)) ]─► t → ⊥
Outputs-no-sndack (sVis refl ())

------------------------------------------------------------------------
-- SIDE STABILITY.
------------------------------------------------------------------------

-- abbreviations for the sync/hide sets at the value level
csSR' csRS' csTA' : EventSet
csSR' = chanSet csSR csSR-dec
csRS' = chanSet csRS csRS-dec
csTA' = chanSet csTA csTA-dec

-- TxSide is τ-stable.  A τ of `(Par⊤ csSR' Inputs TR) ∖ csSR'` is either the
-- inner Par's own τ (→ Inputs / TR stable) or a HIDDEN csSR-event of the inner
-- Par (sndmsg/rcvack); the latter must be a SYNC (event ∈ csSR'), and Inputs
-- offers neither sndmsg nor rcvack ⇒ contradiction.
TxSide-stable : ∀ {t} → TxSide ─[ τ ]─► t → ⊥
TxSide-stable step
  with Hide-τ-elim csSR' (Par⊤ csSR' Inputs (Transmitter ⦀ RcvAck)) step
... | hτP _ parτ _
      with Par-τ-elim csSR' ⊤merge Inputs (Transmitter ⦀ RcvAck) parτ
...   | τL _ Iτ  _ = Inputs-stable Iτ
...   | τR _ TRτ _ = TR-stable TRτ
TxSide-stable step
  | hτH {B} {e} {a} _ mem parev _
      with e
...   | sndmsg id c with Par-ev-elim csSR' ⊤merge Inputs (Transmitter ⦀ RcvAck) parev
...     | evSync _ Iev _ = Inputs-no-sndmsg Iev
...     | evL  ¬cs _   = ¬cs mem
...     | evR  ¬cs _   = ¬cs mem
...     | evBoth ¬cs _ _ = ¬cs mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _
      | rcvack id c with Par-ev-elim csSR' ⊤merge Inputs (Transmitter ⦀ RcvAck) parev
...     | evSync _ Iev _ = Inputs-no-rcvack Iev
...     | evL  ¬cs _   = ¬cs mem
...     | evR  ¬cs _   = ¬cs mem
...     | evBoth ¬cs _ _ = ¬cs mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | input id c = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | output id c = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | rcvmsg id c = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | tx id c = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | sndack id c = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | ack id c = mem

-- Receiver offers only `tx`; SndAck offers only `sndack`.  Neither offers rcvmsg.
Receiver-no-rcvmsg : ∀ {t a id} {c : Conn id} →
  Receiver ─[ ev (evl (evLabel ⊤ (rcvmsg id c) a)) ]─► t → ⊥
Receiver-no-rcvmsg (sVis refl ())

SndAck-no-rcvmsg : ∀ {t a id} {c : Conn id} →
  SndAck ─[ ev (evl (evLabel ⊤ (rcvmsg id c) a)) ]─► t → ⊥
SndAck-no-rcvmsg (sVis refl ())

RS-no-rcvmsg : ∀ {t a id} {c : Conn id} →
  (Receiver ⦀ SndAck) ─[ ev (evl (evLabel ⊤ (rcvmsg id c) a)) ]─► t → ⊥
RS-no-rcvmsg step with Par-ev-elim ∅ES ⊤merge Receiver SndAck step
... | evSync mem _ _ = mem
... | evL  _ Rev   = Receiver-no-rcvmsg Rev
... | evR  _ Sev   = SndAck-no-rcvmsg Sev
... | evBoth _ Rev _ = Receiver-no-rcvmsg Rev

-- RxSide is τ-stable (symmetric to TxSide; hidden events rcvmsg/sndack).
RxSide-stable : ∀ {t} → RxSide ─[ τ ]─► t → ⊥
RxSide-stable step
  with Hide-τ-elim csRS' (Par⊤ csRS' Outputs (Receiver ⦀ SndAck)) step
... | hτP _ parτ _
      with Par-τ-elim csRS' ⊤merge Outputs (Receiver ⦀ SndAck) parτ
...   | τL _ Oτ  _ = Outputs-stable Oτ
...   | τR _ RSτ _ = RS-stable RSτ
RxSide-stable step
  | hτH {B} {e} {a} _ mem parev _
      with e
...   | rcvmsg id c with Par-ev-elim csRS' ⊤merge Outputs (Receiver ⦀ SndAck) parev
...     | evSync _ _ RSev = RS-no-rcvmsg RSev
...     | evL  ¬cs _   = ¬cs mem
...     | evR  ¬cs _   = ¬cs mem
...     | evBoth ¬cs _ _ = ¬cs mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _
      | sndack id c with Par-ev-elim csRS' ⊤merge Outputs (Receiver ⦀ SndAck) parev
...     | evSync _ Oev _ = Outputs-no-sndack Oev
...     | evL  ¬cs _   = ¬cs mem
...     | evR  ¬cs _   = ¬cs mem
...     | evBoth ¬cs _ _ = ¬cs mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | input id c  = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | output id c = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | sndmsg id c = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | tx id c     = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | rcvack id c = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | ack id c    = mem

------------------------------------------------------------------------
-- SIDE NON-OFFER of the top sync events tx / ack.
--   TxSide offers input + ack (after hiding) but NOT tx.
--   RxSide offers output + tx (after hiding) but NOT ack.
------------------------------------------------------------------------

-- leaf/operand refusals of `tx`
Inputs-no-tx : ∀ {t a id} {c : Conn id} →
  Inputs ─[ ev (evl (evLabel ⊤ (tx id c) a)) ]─► t → ⊥
Inputs-no-tx (sVis refl ())

Transmitter-no-tx : ∀ {t a id} {c : Conn id} →
  Transmitter ─[ ev (evl (evLabel ⊤ (tx id c) a)) ]─► t → ⊥
Transmitter-no-tx (sVis refl ())

RcvAck-no-tx : ∀ {t a id} {c : Conn id} →
  RcvAck ─[ ev (evl (evLabel ⊤ (tx id c) a)) ]─► t → ⊥
RcvAck-no-tx (sVis refl ())

TR-no-tx : ∀ {t a id} {c : Conn id} →
  (Transmitter ⦀ RcvAck) ─[ ev (evl (evLabel ⊤ (tx id c) a)) ]─► t → ⊥
TR-no-tx step with Par-ev-elim ∅ES ⊤merge Transmitter RcvAck step
... | evSync mem _ _ = mem
... | evL  _ Tev   = Transmitter-no-tx Tev
... | evR  _ Rev   = RcvAck-no-tx Rev
... | evBoth _ Tev _ = Transmitter-no-tx Tev

-- TxSide does not offer `tx`.
TxSide-no-tx : ∀ {t a id} {c : Conn id} →
  TxSide ─[ ev (evl (evLabel ⊤ (tx id c) a)) ]─► t → ⊥
TxSide-no-tx step
  with Hide-ev-elim csSR' (Par⊤ csSR' Inputs (Transmitter ⦀ RcvAck)) step
... | heV _ _ parev with Par-ev-elim csSR' ⊤merge Inputs (Transmitter ⦀ RcvAck) parev
...   | evSync mem _ _ = mem
...   | evL  _ Iev   = Inputs-no-tx Iev
...   | evR  _ TRev  = TR-no-tx TRev
...   | evBoth _ Iev _ = Inputs-no-tx Iev

-- leaf/operand refusals of `ack`
Outputs-no-ack : ∀ {t a id} {c : Conn id} →
  Outputs ─[ ev (evl (evLabel ⊤ (ack id c) a)) ]─► t → ⊥
Outputs-no-ack (sVis refl ())

Receiver-no-ack : ∀ {t a id} {c : Conn id} →
  Receiver ─[ ev (evl (evLabel ⊤ (ack id c) a)) ]─► t → ⊥
Receiver-no-ack (sVis refl ())

SndAck-no-ack : ∀ {t a id} {c : Conn id} →
  SndAck ─[ ev (evl (evLabel ⊤ (ack id c) a)) ]─► t → ⊥
SndAck-no-ack (sVis refl ())

RS-no-ack : ∀ {t a id} {c : Conn id} →
  (Receiver ⦀ SndAck) ─[ ev (evl (evLabel ⊤ (ack id c) a)) ]─► t → ⊥
RS-no-ack step with Par-ev-elim ∅ES ⊤merge Receiver SndAck step
... | evSync mem _ _ = mem
... | evL  _ Rev   = Receiver-no-ack Rev
... | evR  _ Sev   = SndAck-no-ack Sev
... | evBoth _ Rev _ = Receiver-no-ack Rev

-- RxSide does not offer `ack`.
RxSide-no-ack : ∀ {t a id} {c : Conn id} →
  RxSide ─[ ev (evl (evLabel ⊤ (ack id c) a)) ]─► t → ⊥
RxSide-no-ack step
  with Hide-ev-elim csRS' (Par⊤ csRS' Outputs (Receiver ⦀ SndAck)) step
... | heV _ _ parev with Par-ev-elim csRS' ⊤merge Outputs (Receiver ⦀ SndAck) parev
...   | evSync mem _ _ = mem
...   | evL  _ Oev   = Outputs-no-ack Oev
...   | evR  _ RSev  = RS-no-ack RSev
...   | evBoth _ Oev _ = Outputs-no-ack Oev

------------------------------------------------------------------------
-- TOP modulo-csTA STABILITY.
--   A modulo-csTA step of `Par⊤ csTA' TxSide RxSide` is either
--     · a τ of the inner Par (→ TxSide / RxSide stable), or
--     · a hidden csTA-event (tx/ack): such an event is in csTA' so must be a
--       SYNC, but TxSide refuses tx and RxSide refuses ack ⇒ contradiction.
------------------------------------------------------------------------

Top-noModA : ∀ {t} →
  ModAStep csTA' (Par⊤ csTA' TxSide RxSide) t → ⊥
Top-noModA (maτ parτ) with Par-τ-elim csTA' ⊤merge TxSide RxSide parτ
... | τL _ Tτ _ = TxSide-stable Tτ
... | τR _ Rτ _ = RxSide-stable Rτ
Top-noModA (maE {B} {e} {a} mem parev) with e
... | tx id c with Par-ev-elim csTA' ⊤merge TxSide RxSide parev
...   | evSync _ Txev _ = TxSide-no-tx Txev
...   | evL  ¬cs _    = ¬cs mem
...   | evR  ¬cs _    = ¬cs mem
...   | evBoth ¬cs _ _ = ¬cs mem
Top-noModA (maE {B} {e} {a} mem parev) | ack id c
      with Par-ev-elim csTA' ⊤merge TxSide RxSide parev
...   | evSync _ _ Rxev = RxSide-no-ack Rxev
...   | evL  ¬cs _    = ¬cs mem
...   | evR  ¬cs _    = ¬cs mem
...   | evBoth ¬cs _ _ = ¬cs mem
Top-noModA (maE {B} {e} {a} mem parev) | input id c  = mem
Top-noModA (maE {B} {e} {a} mem parev) | output id c = mem
Top-noModA (maE {B} {e} {a} mem parev) | sndmsg id c = mem
Top-noModA (maE {B} {e} {a} mem parev) | rcvmsg id c = mem
Top-noModA (maE {B} {e} {a} mem parev) | sndack id c = mem
Top-noModA (maE {B} {e} {a} mem parev) | rcvack id c = mem

Top-MAcc : MAcc csTA' (Par⊤ csTA' TxSide RxSide)
Top-MAcc = macc (λ step → ⊥-elim (Top-noModA step))

------------------------------------------------------------------------
-- MILESTONE 1 RESULT.  `Network = (Par⊤ csTA' TxSide RxSide) ∖ csTA'` is the
-- hide of a modulo-csTA accessible process, hence non-divergent.
------------------------------------------------------------------------

¬Diverges-Network : ¬ Diverges Network
¬Diverges-Network =
  Hide-noDiv-from-MAcc csTA' (Par⊤ csTA' TxSide RxSide) Top-MAcc

------------------------------------------------------------------------
-- Network is τ-stable at its initial (deadlocked) state: a τ of
-- `T ∖ csTA'` reflects to a modulo-csTA step of T, which `Top-noModA`
-- refutes.  (Reusable building block for the reachability analysis.)
------------------------------------------------------------------------

Network-noτ : ∀ {t} → Network ─[ τ ]─► t → ⊥
Network-noτ step with Hide-τ-elim csTA' (Par⊤ csTA' TxSide RxSide) step
... | hτP _ parτ _      = Top-noModA (maτ parτ)
... | hτH _ mem parev _ = Top-noModA (maE mem parev)

------------------------------------------------------------------------
-- MILESTONE 2: `CopySpec ⊑D Network` via REACHABLE divergence-freedom.
--
-- `CopySpec ⊑D Network = ∀{s} → divergences Network s → divergences CopySpec s`.
-- A `divergences Network s` carries a `witness W` with `Network ⟹⟨prefix⟩ W` and
-- `Diverges W`.  We show NO weakly-reachable `W` diverges, so `divergences Network`
-- is empty and the inclusion is vacuous.
--
-- The invariant `GoodU T` (on the UN-hidden composite `T`) says: `T` is modulo-csTA
-- accessible (`MAcc csTA' T`, hence `T ∖ csTA'` does not diverge) AND every step of
-- the hidden `T ∖ csTA'` lands again in a `GoodU`-underlying (or `deadlock`).  A step
-- of `T ∖ csTA'` reflects (Hide-{τ,ev}-elim) to one of:
--   · a τ of `T`                        → ModAStep `maτ`   (forward / loop-back hidden)
--   · a hidden csTA-event of `T`         → ModAStep `maE`   (the tx/ack syncs, hidden)
--   · a NON-csTA visible event of `T`    → a visible `input`/`output` step
--   · `√` (force T ≡ ret r)              → lands on `deadlock` (never diverges)
-- so `GoodU` closure is over `UStep` = (ModAStep csTA') ⊎ (visible non-csTA step).
------------------------------------------------------------------------

-- The combined underlying step relation `GoodU` must be closed under.
data UStep (T T′ : NetProc) : Set₁ where
  uMod : ModAStep csTA' T T′ → UStep T T′
  uVis : {B : Set} {e : Net ⊤ B} {a : B}
       → ¬ csTA' .mem (B , e) a
       → T ─[ ev (evl (evLabel B e a)) ]─► T′ → UStep T T′

-- The invariant on un-hidden composite states.
record GoodU (T : NetProc) : Set₁ where
  coinductive
  field
    gmacc : MAcc csTA' T
    gstep : ∀ {T′} → UStep T T′ → GoodU T′
open GoodU

-- A `GoodU` underlying state yields a non-divergent hidden state.
GoodU→noDiv : ∀ {T} → GoodU T → ¬ Diverges (T ∖ csTA')
GoodU→noDiv g = Hide-noDiv-from-MAcc csTA' _ (g .gmacc)

-- after a `√`, the hidden run continues from `deadlock`, which cannot move,
-- so the only continuation is `⟹-refl` and `W = deadlock` is non-divergent.
-- a stable head (no τ, no ev, only `⟹-refl`) cannot start a weak run to a divergent
-- state — generalised so the `⟹-refl` match identifies the source with the target.
stable-no-div-run : ∀ {P : NetProc} {s} {W : NetProc}
                  → (∀ {t} → P ─[ τ ]─► t → ⊥)
                  → (∀ {t e} → P ─[ ev e ]─► t → ⊥)
                  → ¬ Diverges P → P ⟹⟨ s ⟩ W → Diverges W → ⊥
stable-no-div-run nτ nev nd ⟹-refl       dW = nd dW
stable-no-div-run nτ nev nd (⟹-τ st _)   dW = nτ st
stable-no-div-run nτ nev nd (⟹-ev st _)  dW = nev st

deadlock-no-div-run : ∀ {s} {W : NetProc} → deadlock ⟹⟨ s ⟩ W → Diverges W → ⊥
deadlock-no-div-run = stable-no-div-run deadlock-no-τ deadlock-no-ev deadlock-converges

-- The reachability engine: every weak run out of a `GoodU`-hidden state ends at a
-- non-divergent state.  Induct on the run, reflecting each hide-step to a `UStep`
-- (or to `deadlock` on `√`) and walking `GoodU`'s closure.
Reach-noDiv : ∀ {T s W} → GoodU T → (T ∖ csTA') ⟹⟨ s ⟩ W → ¬ Diverges W
Reach-noDiv g ⟹-refl              = GoodU→noDiv g
Reach-noDiv {T = T} g (⟹-τ step rest) with Hide-τ-elim csTA' T step
... | hτP T′ Tτ refl        = Reach-noDiv (g .gstep (uMod (maτ Tτ))) rest
... | hτH T′ mem Tev refl   = Reach-noDiv (g .gstep (uMod (maE mem Tev))) rest
Reach-noDiv {T = T} g (⟹-ev step rest) with Hide-ev-elim csTA' T step
... | heV T′ ¬cs Tev        = Reach-noDiv (g .gstep (uVis ¬cs Tev)) rest
... | he√ _                 = deadlock-no-div-run rest

------------------------------------------------------------------------
-- PHASE A: the UN-HIDDEN composite state walk.
--
-- `T = Par⊤ csTA' TxSide RxSide` is `Network` WITHOUT the outer `∖ csTA'`.
-- We pin the finite sequence of reachable un-hidden states `U0 … U8`
-- (plus the post-loop `sil`-guard chain back to `U0`) along ONE full
-- single-message cycle, with explicit `UStep`-flavoured witnesses.
--
-- KEY DIFFERENCE from the N-states: at the un-hidden level the outer csTA
-- hide is absent, so
--   · the hidden-inside-side τ's (sndmsg/rcvmsg/sndack/rcvack) lose ONE
--     outer `pair fin …` of index nesting (the old outer-hide tag0);
--   · the `tx`/`ack` SYNCS are VISIBLE events of T (sVis), NOT τ's — they
--     are only turned into τ by Network's outer `∖ csTA'`.
------------------------------------------------------------------------

-- τ-branch extractor (analogue of `vis-of` for the silent part).
tau-of : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR
       → (i : AnyTypes (ExtI (Net ⊤))) → proj₁ i → Maybe NetProc
tau-of (react _ τc) = τc
tau-of _            = λ _ _ → nothing

-- τ-successor of `p` along index `i`/value `a` (identity if no such τ).
succτ : NetProc → (i : AnyTypes (ExtI (Net ⊤))) → proj₁ i → NetProc
succτ p i a with tau-of (force p) i a
... | just t  = t
... | nothing = p

-- visible successor of `p` along `at`/`a` (identity if not offered).
succV : NetProc → (at : AnyTypes (Net ⊤)) → proj₁ at → NetProc
succV p at a with vis-of (force p) at a
... | just t  = t
... | nothing = p

T : NetProc
T = Par⊤ csTA' TxSide RxSide

-- U0 = the un-hidden composite.
U0 : NetProc
U0 = T

-- U0 offers `input` (and not `output`); same head shape as Network's offer
-- since the outer hide passes a non-csTA visible event straight through.
U0-offers-input : is-just (vis-of (force U0) inputAt tt) ≡ true
U0-offers-input = refl

U0-no-output : vis-of (force U0) outputAt tt ≡ nothing
U0-no-output = refl

-- U1 := the input-successor of U0.
U1 : NetProc
U1 = succV U0 inputAt tt

U0─input─►U1 : U0 ─[ ev inputLbl ]─► U1
U0─input─►U1 = sVis {at = inputAt} refl refl

-- First hidden τ: U1 fires the hidden `sndmsg` inside TxSide.  Index at the
-- un-hidden level: T-Par tag0 (P=TxSide) → TxSide-hide tag1 (newly hidden
-- sndmsg at `base`).  ONE fewer `pair fin` than Network's `sndmsgIdx`.
sndmsgIdxU : AnyTypes (ExtI (Net ⊤))
sndmsgIdxU = _ , pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (sndmsg N2N_KeepAlive c0)))
sndmsgValU : proj₁ sndmsgIdxU
sndmsgValU = lift fz , (lift (fs fz) , tt)

U2 : NetProc
U2 = succτ U1 sndmsgIdxU sndmsgValU

U1─τ─►U2 : U1 ─[ τ ]─► U2
U1─τ─►U2 = sTau {i = sndmsgIdxU} {a = sndmsgValU} refl refl

-- Second step: U2 fires `tx` as a VISIBLE sync between TxSide and RxSide.
-- At the un-hidden level this is `sVis`, NOT `sTau` (no outer hide).
txAt : AnyTypes (Net ⊤)
txAt = (⊤ , tx N2N_KeepAlive c0)

txLbl : Event√ NetR
txLbl = evl (evLabel ⊤ (tx N2N_KeepAlive c0) tt)

U2-offers-tx : is-just (vis-of (force U2) txAt tt) ≡ true
U2-offers-tx = refl

U3 : NetProc
U3 = succV U2 txAt tt

U2─tx─►U3 : U2 ─[ ev txLbl ]─► U3
U2─tx─►U3 = sVis {at = txAt} refl refl

-- Third step: U3 fires hidden `rcvmsg` inside RxSide.  T-Par tag1 (Q=RxSide)
-- → RxSide-hide tag1 (newly hidden rcvmsg at `base`).
rcvmsgIdxU : AnyTypes (ExtI (Net ⊤))
rcvmsgIdxU = _ , pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (rcvmsg N2N_KeepAlive c0)))
rcvmsgValU : proj₁ rcvmsgIdxU
rcvmsgValU = lift (fs fz) , (lift (fs fz) , tt)

U4 : NetProc
U4 = succτ U3 rcvmsgIdxU rcvmsgValU

U3─τ─►U4 : U3 ─[ τ ]─► U4
U3─τ─►U4 = sTau {i = rcvmsgIdxU} {a = rcvmsgValU} refl refl

-- U4 now offers `output` (and no longer `input`).
U4-offers-output : is-just (vis-of (force U4) outputAt tt) ≡ true
U4-offers-output = refl

U4-no-input : vis-of (force U4) inputAt tt ≡ nothing
U4-no-input = refl

-- U5 := the output-successor of U4.
U5 : NetProc
U5 = succV U4 outputAt tt

U4─output─►U5 : U4 ─[ ev outputLbl ]─► U5
U4─output─►U5 = sVis {at = outputAt} refl refl

-- Back path.  U5 fires hidden `sndack` inside RxSide (T-Par tag1, RxSide-hide
-- tag1, base sndack).
sndackIdxU : AnyTypes (ExtI (Net ⊤))
sndackIdxU = _ , pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (sndack N2N_KeepAlive c0)))
sndackValU : proj₁ sndackIdxU
sndackValU = lift (fs fz) , (lift (fs fz) , tt)

U6 : NetProc
U6 = succτ U5 sndackIdxU sndackValU

U5─τ─►U6 : U5 ─[ τ ]─► U6
U5─τ─►U6 = sTau {i = sndackIdxU} {a = sndackValU} refl refl

-- U6 fires `ack` as a VISIBLE sync between RxSide and TxSide.
ackAt : AnyTypes (Net ⊤)
ackAt = (⊤ , ack N2N_KeepAlive c0)

ackLbl : Event√ NetR
ackLbl = evl (evLabel ⊤ (ack N2N_KeepAlive c0) tt)

U6-offers-ack : is-just (vis-of (force U6) ackAt tt) ≡ true
U6-offers-ack = refl

U7 : NetProc
U7 = succV U6 ackAt tt

U6─ack─►U7 : U6 ─[ ev ackLbl ]─► U7
U6─ack─►U7 = sVis {at = ackAt} refl refl

-- U7 fires hidden `rcvack` inside TxSide (T-Par tag0=P=TxSide, TxSide-hide
-- tag1, base rcvack).
rcvackIdxU : AnyTypes (ExtI (Net ⊤))
rcvackIdxU = _ , pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (rcvack N2N_KeepAlive c0)))
rcvackValU : proj₁ rcvackIdxU
rcvackValU = lift fz , (lift (fs fz) , tt)

U8 : NetProc
U8 = succτ U7 rcvackIdxU rcvackValU

U7─τ─►U8 : U7 ─[ τ ]─► U8
U7─τ─►U8 = sTau {i = rcvackIdxU} {a = rcvackValU} refl refl

-- PROBE: U8 offers neither input nor output (it is a guard mid-state).
U8-no-input  : vis-of (force U8) inputAt  tt ≡ nothing
U8-no-input  = refl
U8-no-output : vis-of (force U8) outputAt tt ≡ nothing
U8-no-output = refl

-- guard τ: resolve the looped RcvAck leaf inside TxSide.
-- T-Par tag0 (TxSide) → TxSide-hide tag0 (own τ) → csSR'-Par tag1 (TR side)
-- → TR-Par tag1 (RcvAck) → leaf `fin` sil-guard.
g1Idx : AnyTypes (ExtI (Net ⊤))
g1Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2})
              (pair (fin {n = 2}) (fin {n = 1}))))
g1Val : proj₁ g1Idx
g1Val = lift fz , (lift fz , (lift (fs fz) , (lift (fs fz) , lift fz)))

U8a : NetProc
U8a = succτ U8 g1Idx g1Val

U8─τ─►U8a : U8 ─[ τ ]─► U8a
U8─τ─►U8a = sTau {i = g1Idx} {a = g1Val} refl refl

-- guard τ #2: resolve the looped Transmitter leaf (TxSide / TR-Par tag0).
g2Idx : AnyTypes (ExtI (Net ⊤))
g2Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2})
              (pair (fin {n = 2}) (fin {n = 1}))))
g2Val : proj₁ g2Idx
g2Val = lift fz , (lift fz , (lift (fs fz) , (lift fz , lift fz)))

U8b : NetProc
U8b = succτ U8a g2Idx g2Val

U8a─τ─►U8b : U8a ─[ τ ]─► U8b
U8a─τ─►U8b = sTau {i = g2Idx} {a = g2Val} refl refl

-- guard τ #3: resolve the looped Input leaf (TxSide / Inputs side; the
-- Skip-padded `⦀⋆`/`⦀` chain collapses, so NO extra tag layers — the leaf
-- sil sits directly under csSR'-Par tag0).
g3Idx : AnyTypes (ExtI (Net ⊤))
g3Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2}) (fin {n = 1})))
g3Val : proj₁ g3Idx
g3Val = lift fz , (lift fz , (lift fz , lift fz))

U8c : NetProc
U8c = succτ U8b g3Idx g3Val

U8b─τ─►U8c : U8b ─[ τ ]─► U8c
U8b─τ─►U8c = sTau {i = g3Idx} {a = g3Val} refl refl

-- guard τ #4: resolve the looped Output leaf (RxSide / Outputs side; same
-- collapse as Inputs).
g4Idx : AnyTypes (ExtI (Net ⊤))
g4Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2}) (fin {n = 1})))
g4Val : proj₁ g4Idx
g4Val = lift (fs fz) , (lift fz , (lift fz , lift fz))

U8d : NetProc
U8d = succτ U8c g4Idx g4Val

U8c─τ─►U8d : U8c ─[ τ ]─► U8d
U8c─τ─►U8d = sTau {i = g4Idx} {a = g4Val} refl refl

-- guard τ #5: resolve the looped Receiver leaf (RxSide / RS-Par tag0).
g5Idx : AnyTypes (ExtI (Net ⊤))
g5Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2})
              (pair (fin {n = 2}) (fin {n = 1}))))
g5Val : proj₁ g5Idx
g5Val = lift (fs fz) , (lift fz , (lift (fs fz) , (lift fz , lift fz)))

U8e : NetProc
U8e = succτ U8d g5Idx g5Val

U8d─τ─►U8e : U8d ─[ τ ]─► U8e
U8d─τ─►U8e = sTau {i = g5Idx} {a = g5Val} refl refl

-- guard τ #6: resolve the looped SndAck leaf (RxSide / RS-Par tag1).
g6Idx : AnyTypes (ExtI (Net ⊤))
g6Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2})
              (pair (fin {n = 2}) (fin {n = 1}))))
g6Val : proj₁ g6Idx
g6Val = lift (fs fz) , (lift fz , (lift (fs fz) , (lift (fs fz) , lift fz)))

U8f : NetProc
U8f = succτ U8e g6Idx g6Val

U8e─τ─►U8f : U8e ─[ τ ]─► U8f
U8e─τ─►U8f = sTau {i = g6Idx} {a = g6Val} refl refl

-- CYCLE CLOSURE: after the six `sil`-guard τ's every looped leaf is back in
-- its original `react`/`loop0`-body form, so U8f is DEFINITIONALLY U0.
U8f≡U0 : U8f ≡ U0
U8f≡U0 = refl

------------------------------------------------------------------------
-- Mid-state visible-offer sanity: every state strictly between the two
-- functional visible events (U1,U2,U3 on the forward path; U5,U6,U7 on the
-- back path; U8 a guard mid-state) offers NEITHER `input` NOR `output`.
-- (U0/U4 are the only states with a visible non-csTA offer; U2/U6 offer the
-- csTA syncs tx/ack, NOT input/output.)
------------------------------------------------------------------------

U1-mid-in  : vis-of (force U1) inputAt  tt ≡ nothing
U1-mid-in  = refl
U1-mid-out : vis-of (force U1) outputAt tt ≡ nothing
U1-mid-out = refl

U2-mid-in  : vis-of (force U2) inputAt  tt ≡ nothing
U2-mid-in  = refl
U2-mid-out : vis-of (force U2) outputAt tt ≡ nothing
U2-mid-out = refl

U3-mid-in  : vis-of (force U3) inputAt  tt ≡ nothing
U3-mid-in  = refl
U3-mid-out : vis-of (force U3) outputAt tt ≡ nothing
U3-mid-out = refl

U5-mid-in  : vis-of (force U5) inputAt  tt ≡ nothing
U5-mid-in  = refl
U5-mid-out : vis-of (force U5) outputAt tt ≡ nothing
U5-mid-out = refl

U6-mid-in  : vis-of (force U6) inputAt  tt ≡ nothing
U6-mid-in  = refl
U6-mid-out : vis-of (force U6) outputAt tt ≡ nothing
U6-mid-out = refl

U7-mid-in  : vis-of (force U7) inputAt  tt ≡ nothing
U7-mid-in  = refl
U7-mid-out : vis-of (force U7) outputAt tt ≡ nothing
U7-mid-out = refl

------------------------------------------------------------------------
-- M2: PARAMETRIC DECODE  `⟦_⟧ : CS → NetProc`.
--
-- Six per-operand position-decode functions, each obtained by REDUCTION
-- (succV / succτ) from the previous position, so each case is DEFINITIONALLY
-- the actual reachable operand term.  The six are assembled into the two
-- sides and the whole via the EXACT operator forms of `Network.agda`, so
-- `⟦ cs ⟧` is definitionally the composite that the Phase-A U-walk reaches.
------------------------------------------------------------------------

-- the bare-leaf visible-offer indices used by the operand reductions
sndmsgAtN rcvackAtN ackAtN rcvmsgAtN sndackAtN : AnyTypes (Net ⊤)
sndmsgAtN = (⊤ , sndmsg N2N_KeepAlive c0)
rcvackAtN = (⊤ , rcvack N2N_KeepAlive c0)
ackAtN    = (⊤ , ack    N2N_KeepAlive c0)
rcvmsgAtN = (⊤ , rcvmsg N2N_KeepAlive c0)
sndackAtN = (⊤ , sndack N2N_KeepAlive c0)

-- `output` is now ambiguous (re-exported twice); reuse the existing `outputAt`.
outputAtN : AnyTypes (Net ⊤)
outputAtN = outputAt

-- Leaf-level guard τ index (a `loop0` body that returned `ret tt` forces to
-- `sil (iter …)`; at the bare-leaf / Skip-padded ⦀ operand level the
-- restart-guard sits directly under the ⦀ tag of that operand).  The decI/decO
-- operands are `⦀⋆`-wrapped so their guard nests one `pair fin` deeper than the
-- bare Transmitter/etc.; the indices below are pinned by the `dec-Ui` probes.

------------------------------------------------------------------------
-- decI : the Inputs operand  ( ⦀⋆ [ Input N2N_KeepAlive c0 ] -form ).
------------------------------------------------------------------------
decI : IP → NetProc
decI I0 = Inputs
decI I1 = succV Inputs inputAt tt
decI I2 = succV (succV Inputs inputAt tt) sndmsgAtN tt
decI Ig = succV (succV (succV Inputs inputAt tt) sndmsgAtN tt) rcvackAtN tt

------------------------------------------------------------------------
-- decT : the Transmitter operand.
------------------------------------------------------------------------
decT : TP → NetProc
decT T0 = Transmitter
decT T1 = succV Transmitter sndmsgAtN tt
decT Tg = succV (succV Transmitter sndmsgAtN tt) txAt tt

------------------------------------------------------------------------
-- decR : the RcvAck operand.
------------------------------------------------------------------------
decR : RP → NetProc
decR R0 = RcvAck
decR R1 = succV RcvAck ackAt tt
decR Rg = succV (succV RcvAck ackAt tt) rcvackAtN tt

------------------------------------------------------------------------
-- decO : the Outputs operand  ( ⦀⋆ [ Output N2N_KeepAlive c0 ] -form ).
------------------------------------------------------------------------
decO : OP → NetProc
decO O0 = Outputs
decO O1 = succV Outputs rcvmsgAtN tt
decO O2 = succV (succV Outputs rcvmsgAtN tt) outputAtN tt
decO Og = succV (succV (succV Outputs rcvmsgAtN tt) outputAtN tt) sndackAtN tt

------------------------------------------------------------------------
-- decC : the Receiver operand.
------------------------------------------------------------------------
decC : CP → NetProc
decC Rc0 = Receiver
decC Rc1 = succV Receiver txAt tt
decC Rcg = succV (succV Receiver txAt tt) rcvmsgAtN tt

------------------------------------------------------------------------
-- decS : the SndAck operand.
------------------------------------------------------------------------
decS : SP → NetProc
decS Sa0 = SndAck
decS Sa1 = succV SndAck sndackAtN tt
decS Sag = succV (succV SndAck sndackAtN tt) ackAtN tt

------------------------------------------------------------------------
-- The two sides and the whole, in the EXACT operator forms of Network.agda.
------------------------------------------------------------------------
decTx : IP → TP → RP → NetProc
decTx i t r = (Par⊤ csSR' (decI i) (decT t ⦀ decR r)) ∖ csSR'

decRx : OP → CP → SP → NetProc
decRx o c s = (Par⊤ csRS' (decO o) (decC c ⦀ decS s)) ∖ csRS'

⟦_⟧ : CS → NetProc
⟦ mkCS i t r o c s ⟧ = Par⊤ csTA' (decTx i t r) (decRx o c s)

------------------------------------------------------------------------
-- VALIDATION (all by `refl`).
------------------------------------------------------------------------
dec-cs0 : ⟦ cs0 ⟧ ≡ T
dec-cs0 = refl

dec-U0 : ⟦ cs0 ⟧ ≡ U0
dec-U0 = refl

dec-U1 : ⟦ mkCS I1 T0 R0 O0 Rc0 Sa0 ⟧ ≡ U1
dec-U1 = refl

dec-U2 : ⟦ mkCS I2 T1 R0 O0 Rc0 Sa0 ⟧ ≡ U2
dec-U2 = refl

dec-U3 : ⟦ mkCS I2 Tg R0 O0 Rc1 Sa0 ⟧ ≡ U3
dec-U3 = refl

dec-U4 : ⟦ mkCS I2 Tg R0 O1 Rcg Sa0 ⟧ ≡ U4
dec-U4 = refl

dec-U5 : ⟦ mkCS I2 Tg R0 O2 Rcg Sa0 ⟧ ≡ U5
dec-U5 = refl

dec-U6 : ⟦ mkCS I2 Tg R0 Og Rcg Sa1 ⟧ ≡ U6
dec-U6 = refl

dec-U7 : ⟦ mkCS I2 Tg R1 Og Rcg Sag ⟧ ≡ U7
dec-U7 = refl

dec-U8 : ⟦ mkCS Ig Tg Rg Og Rcg Sag ⟧ ≡ U8
dec-U8 = refl

------------------------------------------------------------------------
-- M3: PER-LEAF STEP CHARACTERIZATION.
--
-- For each of the six operand decode functions a τ-characterization
-- (which positions admit a τ, and to where) and an ev-characterization
-- (which visible events each position offers, and to where).  Stated as
-- SEPARATE per-position lemmas (easier to prove and to consume in M4).
--
-- Convention for τ at the guard positions: the looped leaf returned `Skip`
-- (`ret tt`), so `iter-bind` forces the term to `sil (iter …)` — i.e. the
-- restart-guard τ is a `sSil refl` (NOT a `sTau`), landing definitionally
-- on the leaf's position-0 form.
------------------------------------------------------------------------

-- generic ev-label builder for the bare-leaf alphabet
evN : {B : Set} → Net ⊤ B → B → Event√ NetR
evN {B} e a = evl (evLabel B e a)

-- `output` is re-exported twice; pin the single intended constructor via a
-- freshly qualified import.
import CSP.Examples.Cardano_network.Net p1 as NetQ

output′ : (id : IDs) → Conn id → Net ⊤ ⊤
output′ = NetQ.output

------------------------------------------------------------------------
-- decT : Transmitter.  T0 --sndmsg--> T1 ; T1 --tx--> Tg ; Tg --τ(sil)--> T0.
------------------------------------------------------------------------

-- T0 offers exactly `sndmsg` (→ T1) and nothing else; no τ.
decT-T0-noτ : ∀ {W} → decT T0 ─[ τ ]─► W → ⊥
decT-T0-noτ = Transmitter-stable

decT-T0-sndmsg : ∀ {a W} →
  decT T0 ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → W ≡ decT T1
decT-T0-sndmsg (sVis refl refl) = refl

-- T1 offers exactly `tx` (→ Tg); no τ.
decT-T1-noτ : ∀ {W} → decT T1 ─[ τ ]─► W → ⊥
decT-T1-noτ (sSil ())
decT-T1-noτ (sTau {i = _ , fin}                 refl ())
decT-T1-noτ (sTau {i = _ , base _}              refl ())
decT-T1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decT-T1-noτ (sTau {i = _ , pair fin fin}        refl ())
decT-T1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decT-T1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decT-T1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decT-T1-tx : ∀ {a W} →
  decT T1 ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → W ≡ decT Tg
decT-T1-tx (sVis refl refl) = refl

-- Tg has the single restart guard τ (sSil, → T0); offers no ev.
decT-Tg-τ : ∀ {W} → decT Tg ─[ τ ]─► W → W ≡ decT T0
decT-Tg-τ (sSil refl) = refl
decT-Tg-τ (sTau () _)

decT-Tg-noev : ∀ {B e a W} →
  decT Tg ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decT-Tg-noev (sVis () _)

------------------------------------------------------------------------
-- decR : RcvAck.  R0 --ack--> R1 ; R1 --rcvack--> Rg ; Rg --τ(sil)--> R0.
------------------------------------------------------------------------

decR-R0-noτ : ∀ {W} → decR R0 ─[ τ ]─► W → ⊥
decR-R0-noτ = RcvAck-stable

decR-R0-ack : ∀ {a W} →
  decR R0 ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → W ≡ decR R1
decR-R0-ack (sVis refl refl) = refl

decR-R1-noτ : ∀ {W} → decR R1 ─[ τ ]─► W → ⊥
decR-R1-noτ (sSil ())
decR-R1-noτ (sTau {i = _ , fin}                 refl ())
decR-R1-noτ (sTau {i = _ , base _}              refl ())
decR-R1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decR-R1-noτ (sTau {i = _ , pair fin fin}        refl ())
decR-R1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decR-R1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decR-R1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decR-R1-rcvack : ∀ {a W} →
  decR R1 ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → W ≡ decR Rg
decR-R1-rcvack (sVis refl refl) = refl

decR-Rg-τ : ∀ {W} → decR Rg ─[ τ ]─► W → W ≡ decR R0
decR-Rg-τ (sSil refl) = refl
decR-Rg-τ (sTau () _)

decR-Rg-noev : ∀ {B e a W} →
  decR Rg ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decR-Rg-noev (sVis () _)

------------------------------------------------------------------------
-- decC : Receiver.  Rc0 --tx--> Rc1 ; Rc1 --rcvmsg--> Rcg ; Rcg --τ(sil)--> Rc0.
------------------------------------------------------------------------

decC-Rc0-noτ : ∀ {W} → decC Rc0 ─[ τ ]─► W → ⊥
decC-Rc0-noτ = Receiver-stable

decC-Rc0-tx : ∀ {a W} →
  decC Rc0 ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → W ≡ decC Rc1
decC-Rc0-tx (sVis refl refl) = refl

decC-Rc1-noτ : ∀ {W} → decC Rc1 ─[ τ ]─► W → ⊥
decC-Rc1-noτ (sSil ())
decC-Rc1-noτ (sTau {i = _ , fin}                 refl ())
decC-Rc1-noτ (sTau {i = _ , base _}              refl ())
decC-Rc1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decC-Rc1-noτ (sTau {i = _ , pair fin fin}        refl ())
decC-Rc1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decC-Rc1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decC-Rc1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decC-Rc1-rcvmsg : ∀ {a W} →
  decC Rc1 ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → W ≡ decC Rcg
decC-Rc1-rcvmsg (sVis refl refl) = refl

decC-Rcg-τ : ∀ {W} → decC Rcg ─[ τ ]─► W → W ≡ decC Rc0
decC-Rcg-τ (sSil refl) = refl
decC-Rcg-τ (sTau () _)

decC-Rcg-noev : ∀ {B e a W} →
  decC Rcg ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decC-Rcg-noev (sVis () _)

------------------------------------------------------------------------
-- decS : SndAck.  Sa0 --sndack--> Sa1 ; Sa1 --ack--> Sag ; Sag --τ(sil)--> Sa0.
------------------------------------------------------------------------

decS-Sa0-noτ : ∀ {W} → decS Sa0 ─[ τ ]─► W → ⊥
decS-Sa0-noτ = SndAck-stable

decS-Sa0-sndack : ∀ {a W} →
  decS Sa0 ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → W ≡ decS Sa1
decS-Sa0-sndack (sVis refl refl) = refl

decS-Sa1-noτ : ∀ {W} → decS Sa1 ─[ τ ]─► W → ⊥
decS-Sa1-noτ (sSil ())
decS-Sa1-noτ (sTau {i = _ , fin}                 refl ())
decS-Sa1-noτ (sTau {i = _ , base _}              refl ())
decS-Sa1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decS-Sa1-noτ (sTau {i = _ , pair fin fin}        refl ())
decS-Sa1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decS-Sa1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decS-Sa1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decS-Sa1-ack : ∀ {a W} →
  decS Sa1 ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → W ≡ decS Sag
decS-Sa1-ack (sVis refl refl) = refl

decS-Sag-τ : ∀ {W} → decS Sag ─[ τ ]─► W → W ≡ decS Sa0
decS-Sag-τ (sSil refl) = refl
decS-Sag-τ (sTau () _)

decS-Sag-noev : ∀ {B e a W} →
  decS Sag ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decS-Sag-noev (sVis () _)

------------------------------------------------------------------------
-- decI : the Inputs operand ( ⦀⋆ [ Input N2N_KeepAlive c0 ] -form ).
--   I0 --input--> I1 ; I1 --sndmsg--> I2 ; I2 --rcvack--> Ig ; Ig --τ--> I0.
-- The ⦀⋆/⦀ Skip-padding collapses, so the active leaf's react surfaces at
-- the top; visible offers fire by `sVis refl refl`, and the restart guard
-- is the leaf `sil` (sSil refl).
------------------------------------------------------------------------

decI-I0-noτ : ∀ {W} → decI I0 ─[ τ ]─► W → ⊥
decI-I0-noτ = Inputs-stable

decI-I0-input : ∀ {a W} →
  decI I0 ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → W ≡ decI I1
decI-I0-input (sVis refl refl) = refl

decI-I1-noτ : ∀ {W} → decI I1 ─[ τ ]─► W → ⊥
decI-I1-noτ (sSil ())
decI-I1-noτ (sTau {i = _ , fin}                 refl ())
decI-I1-noτ (sTau {i = _ , base _}              refl ())
decI-I1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decI-I1-noτ (sTau {i = _ , pair fin fin}        refl ())
decI-I1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decI-I1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decI-I1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decI-I1-sndmsg : ∀ {a W} →
  decI I1 ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → W ≡ decI I2
decI-I1-sndmsg (sVis refl refl) = refl

decI-I2-noτ : ∀ {W} → decI I2 ─[ τ ]─► W → ⊥
decI-I2-noτ (sSil ())
decI-I2-noτ (sTau {i = _ , fin}                 refl ())
decI-I2-noτ (sTau {i = _ , base _}              refl ())
decI-I2-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decI-I2-noτ (sTau {i = _ , pair fin fin}        refl ())
decI-I2-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decI-I2-noτ (sTau {i = _ , pair (base _) _}     refl ())
decI-I2-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decI-I2-rcvack : ∀ {a W} →
  decI I2 ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → W ≡ decI Ig
decI-I2-rcvack (sVis refl refl) = refl

decI-Ig-τ : ∀ {W} → decI Ig ─[ τ ]─► W → W ≡ decI I0
decI-Ig-τ (sSil refl) = refl
decI-Ig-τ (sTau () _)

decI-Ig-noev : ∀ {B e a W} →
  decI Ig ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decI-Ig-noev (sVis () _)

------------------------------------------------------------------------
-- decO : the Outputs operand ( ⦀⋆ [ Output N2N_KeepAlive c0 ] -form ).
--   O0 --rcvmsg--> O1 ; O1 --output--> O2 ; O2 --sndack--> Og ; Og --τ--> O0.
------------------------------------------------------------------------

decO-O0-noτ : ∀ {W} → decO O0 ─[ τ ]─► W → ⊥
decO-O0-noτ = Outputs-stable

decO-O0-rcvmsg : ∀ {a W} →
  decO O0 ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → W ≡ decO O1
decO-O0-rcvmsg (sVis refl refl) = refl

decO-O1-noτ : ∀ {W} → decO O1 ─[ τ ]─► W → ⊥
decO-O1-noτ (sSil ())
decO-O1-noτ (sTau {i = _ , fin}                 refl ())
decO-O1-noτ (sTau {i = _ , base _}              refl ())
decO-O1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decO-O1-noτ (sTau {i = _ , pair fin fin}        refl ())
decO-O1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decO-O1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decO-O1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decO-O1-output : ∀ {a W} →
  decO O1 ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → W ≡ decO O2
decO-O1-output (sVis refl refl) = refl

decO-O2-noτ : ∀ {W} → decO O2 ─[ τ ]─► W → ⊥
decO-O2-noτ (sSil ())
decO-O2-noτ (sTau {i = _ , fin}                 refl ())
decO-O2-noτ (sTau {i = _ , base _}              refl ())
decO-O2-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decO-O2-noτ (sTau {i = _ , pair fin fin}        refl ())
decO-O2-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decO-O2-noτ (sTau {i = _ , pair (base _) _}     refl ())
decO-O2-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decO-O2-sndack : ∀ {a W} →
  decO O2 ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → W ≡ decO Og
decO-O2-sndack (sVis refl refl) = refl

decO-Og-τ : ∀ {W} → decO Og ─[ τ ]─► W → W ≡ decO O0
decO-Og-τ (sSil refl) = refl
decO-Og-τ (sTau () _)

decO-Og-noev : ∀ {B e a W} →
  decO Og ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decO-Og-noev (sVis () _)

------------------------------------------------------------------------
-- M4a: TxSide-level simulation lemmas.
--
--   decTx i t r = (Par⊤ csSR' (decI i) (decT t ⦀ decR r)) ∖ csSR'
--
-- We characterise EVERY LTS step of `decTx i t r` by gluing the M3
-- per-leaf lemmas through the `⦀`, `Par⊤ csSR'`, and `∖ csSR'` layers.
--
-- Two deliverables for M4c:
--   sim-Tx-τ  : every τ of decTx is one of the 5 internal moves
--   sim-Tx-ev : every visible offer of decTx is one of input/tx/ack
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Operand-level τ classifiers: a τ of decI/decT/decR forces the guard
-- position and the loop-back successor (the only τ each operand admits).
------------------------------------------------------------------------

decI-τ-class : ∀ {i W} → decI i ─[ τ ]─► W → (i ≡ Ig) × (W ≡ decI I0)
decI-τ-class {I0} step = ⊥-elim (decI-I0-noτ step)
decI-τ-class {I1} step = ⊥-elim (decI-I1-noτ step)
decI-τ-class {I2} step = ⊥-elim (decI-I2-noτ step)
decI-τ-class {Ig} step = refl , decI-Ig-τ step

decT-τ-class : ∀ {t W} → decT t ─[ τ ]─► W → (t ≡ Tg) × (W ≡ decT T0)
decT-τ-class {T0} step = ⊥-elim (decT-T0-noτ step)
decT-τ-class {T1} step = ⊥-elim (decT-T1-noτ step)
decT-τ-class {Tg} step = refl , decT-Tg-τ step

decR-τ-class : ∀ {r W} → decR r ─[ τ ]─► W → (r ≡ Rg) × (W ≡ decR R0)
decR-τ-class {R0} step = ⊥-elim (decR-R0-noτ step)
decR-τ-class {R1} step = ⊥-elim (decR-R1-noτ step)
decR-τ-class {Rg} step = refl , decR-Rg-τ step

------------------------------------------------------------------------
-- Operand-level event classifiers for the SYNC events (sndmsg / rcvack)
-- and the refutations that the partner operand refuses them.
------------------------------------------------------------------------

-- decI offers `sndmsg` only at I1 (→ I2); refuse it at I0/I2/Ig.
decI-sndmsg-class : ∀ {i a W} →
  decI i ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → (i ≡ I1) × (W ≡ decI I2)
decI-sndmsg-class {I0} (sVis refl ())
decI-sndmsg-class {I1} step = refl , decI-I1-sndmsg step
decI-sndmsg-class {I2} (sVis refl ())
decI-sndmsg-class {Ig} step = ⊥-elim (decI-Ig-noev step)

-- decI offers `rcvack` only at I2 (→ Ig); refuse it at I0/I1/Ig.
decI-rcvack-class : ∀ {i a W} →
  decI i ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → (i ≡ I2) × (W ≡ decI Ig)
decI-rcvack-class {I0} (sVis refl ())
decI-rcvack-class {I1} (sVis refl ())
decI-rcvack-class {I2} step = refl , decI-I2-rcvack step
decI-rcvack-class {Ig} step = ⊥-elim (decI-Ig-noev step)

-- decT offers `sndmsg` only at T0 (→ T1); refuse it at T1/Tg.
decT-sndmsg-class : ∀ {t a W} →
  decT t ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → (t ≡ T0) × (W ≡ decT T1)
decT-sndmsg-class {T0} step = refl , decT-T0-sndmsg step
decT-sndmsg-class {T1} (sVis refl ())
decT-sndmsg-class {Tg} step = ⊥-elim (decT-Tg-noev step)

-- decT refuses `rcvack` everywhere (it offers only sndmsg / tx).
decT-no-rcvack : ∀ {t a W} →
  decT t ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-rcvack {T0} (sVis refl ())
decT-no-rcvack {T1} (sVis refl ())
decT-no-rcvack {Tg} step = decT-Tg-noev step

-- decR offers `rcvack` only at R1 (→ Rg); refuse it at R0/Rg.
decR-rcvack-class : ∀ {r a W} →
  decR r ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → (r ≡ R1) × (W ≡ decR Rg)
decR-rcvack-class {R0} (sVis refl ())
decR-rcvack-class {R1} step = refl , decR-R1-rcvack step
decR-rcvack-class {Rg} step = ⊥-elim (decR-Rg-noev step)

-- decR refuses `sndmsg` everywhere (it offers only ack / rcvack).
decR-no-sndmsg : ∀ {r a W} →
  decR r ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-sndmsg {R0} (sVis refl ())
decR-no-sndmsg {R1} (sVis refl ())
decR-no-sndmsg {Rg} step = decR-Rg-noev step

------------------------------------------------------------------------
-- TR = decT t ⦀ decR r  (the inner interleaving inside TxSide).
-- Classify its τ's and its sndmsg/rcvack syncs through `Par-ev/τ-elim ∅ES`.
------------------------------------------------------------------------

-- A τ of (decT t ⦀ decR r) is either decT's guard (t=Tg, →T0) keeping decR,
-- or decR's guard (r=Rg, →R0) keeping decT.
TR-τ-class : ∀ {t r W} → (decT t ⦀ decR r) ─[ τ ]─► W →
    ((t ≡ Tg) × (W ≡ (decT T0 ⦀ decR r)))
  ⊎ ((r ≡ Rg) × (W ≡ (decT t  ⦀ decR R0)))
TR-τ-class {t} {r} step with Par-τ-elim ∅ES ⊤merge (decT t) (decR r) step
... | τL P′ Tτ refl = inj₁ (proj₁ cl , cong (λ z → z ⦀ decR r) (proj₂ cl))
  where cl = decT-τ-class Tτ
... | τR Q′ Rτ refl = inj₂ (proj₁ cl , cong (λ z → decT t ⦀ z) (proj₂ cl))
  where cl = decR-τ-class Rτ

-- The sndmsg sync of TR: decT accepts (T0→T1); decR refuses ⇒ it is a
-- decT-solo (evR/evBoth impossible because decR refuses; evSync needs ∅ES
-- membership which is ⊥).
TR-sndmsg-class : ∀ {t r a W} →
  (decT t ⦀ decR r) ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W →
  (t ≡ T0) × (W ≡ (decT T1 ⦀ decR r))
TR-sndmsg-class {t} {r} step
  with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = proj₁ cl , cong (λ z → z ⦀ decR r) (proj₂ cl)
  where cl = decT-sndmsg-class {t} Tev
TR-sndmsg-class {t} {r} step | evR  _ Rev = ⊥-elim (decR-no-sndmsg {r} Rev)
TR-sndmsg-class {t} {r} step | evBoth _ Tev Rev = ⊥-elim (decR-no-sndmsg {r} Rev)

-- The rcvack sync of TR: decR offers (R1→Rg); decT refuses ⇒ decR-solo.
TR-rcvack-class : ∀ {t r a W} →
  (decT t ⦀ decR r) ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W →
  (r ≡ R1) × (W ≡ (decT t ⦀ decR Rg))
TR-rcvack-class {t} {r} step
  with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = ⊥-elim (decT-no-rcvack {t} Tev)
TR-rcvack-class {t} {r} step | evR  _ Rev = proj₁ cl , cong (λ z → decT t ⦀ z) (proj₂ cl)
  where cl = decR-rcvack-class {r} Rev
TR-rcvack-class {t} {r} step | evBoth _ Tev _ = ⊥-elim (decT-no-rcvack {t} Tev)

------------------------------------------------------------------------
-- sim-Tx-τ : characterise every τ of decTx i t r.
--   internal moves: sndmsg-sync, rcvack-sync, guard gI, guard gT, guard gR.
------------------------------------------------------------------------

sim-Tx-τ : ∀ {i t r W} → decTx i t r ─[ τ ]─► W →
    ((i ≡ I1) × (t ≡ T0) × (W ≡ decTx I2 T1 r))    -- sndmsg sync
  ⊎ ((r ≡ R1) × (i ≡ I2) × (W ≡ decTx Ig t Rg))     -- rcvack sync
  ⊎ ((i ≡ Ig) × (W ≡ decTx I0 t r))                 -- guard gI
  ⊎ ((t ≡ Tg) × (W ≡ decTx i T0 r))                 -- guard gT
  ⊎ ((r ≡ Rg) × (W ≡ decTx i t R0))                 -- guard gR
sim-Tx-τ {i} {t} {r} step
  with Hide-τ-elim csSR' (Par⊤ csSR' (decI i) (decT t ⦀ decR r)) step
-- (A) the inner Par's own τ: decI guard, or a τ of TR (decT/decR guard).
... | hτP _ parτ refl
      with Par-τ-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parτ
...   | τL _ Iτ refl =
        inj₂ (inj₂ (inj₁ (proj₁ cl ,
          cong (λ z → (Par⊤ csSR' z (decT t ⦀ decR r)) ∖ csSR') (proj₂ cl))))
  where cl = decI-τ-class Iτ
sim-Tx-τ {i} {t} {r} step | hτP _ parτ refl
      | τR _ TRτ refl with TR-τ-class TRτ
...     | inj₁ (gt , weq) =
          inj₂ (inj₂ (inj₂ (inj₁ (gt ,
            cong (λ z → (Par⊤ csSR' (decI i) z) ∖ csSR') weq))))
...     | inj₂ (gr , weq) =
          inj₂ (inj₂ (inj₂ (inj₂ (gr ,
            cong (λ z → (Par⊤ csSR' (decI i) z) ∖ csSR') weq))))
-- (B) a HIDDEN csSR-event of the inner Par: a sndmsg or rcvack SYNC.
sim-Tx-τ {i} {t} {r} step
  | hτH {B} {e} {a} _ mem parev refl with e
-- sndmsg sync: only N2N_KeepAlive has a connection (Conn id = Fin 0 elsewhere),
-- and Conn N2N_KeepAlive = Fin 1 = {zero=c0}; pin id/c, then classify.
... | sndmsg N2N_ChainSync    ()
... | sndmsg N2N_BlockFetch   ()
... | sndmsg N2N_TxSubmission ()
... | sndmsg N2N_LeiosNotify  ()
... | sndmsg N2N_LeiosFetch   ()
... | sndmsg N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync _ Iev TRev = inj₁ (proj₁ clI , proj₁ clTR ,
          cong₂ (λ z w → (Par⊤ csSR' z w) ∖ csSR') (proj₂ clI) (proj₂ clTR))
  where clI  = decI-sndmsg-class {i} Iev
        clTR = TR-sndmsg-class {t} {r} TRev
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg N2N_KeepAlive zero
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg N2N_KeepAlive zero
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg N2N_KeepAlive zero
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
-- rcvack sync: same id/c pinning.
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_ChainSync    ()
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_BlockFetch   ()
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_TxSubmission ()
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_LeiosNotify  ()
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_LeiosFetch   ()
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync _ Iev TRev = inj₂ (inj₁ (proj₁ clR , proj₁ clI ,
          cong₂ (λ z w → (Par⊤ csSR' z w) ∖ csSR') (proj₂ clI) (proj₂ clR)))
  where clI = decI-rcvack-class {i} Iev
        clR = TR-rcvack-class {t} {r} TRev
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_KeepAlive zero
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_KeepAlive zero
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_KeepAlive zero
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
-- non-csSR constructors: `mem : csSR' .mem (B,e) a = ⊥`.
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | input id c  = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | output id c = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg id c = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | tx id c     = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndack id c = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | ack id c    = ⊥-elim mem

------------------------------------------------------------------------
-- Operand-level visible-offer classifiers / refutations for the NON-csSR
-- events (input on decI; tx / ack on the TR side).  Fixed at the channel
-- `N2N_KeepAlive c0`; id-pinning is done at the sim-Tx-ev call site.
------------------------------------------------------------------------

-- decI offers `input` only at I0 (→ I1).
decI-input-class : ∀ {i a W} →
  decI i ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → (i ≡ I0) × (W ≡ decI I1)
decI-input-class {I0} step = refl , decI-I0-input step
decI-input-class {I1} (sVis refl ())
decI-input-class {I2} (sVis refl ())
decI-input-class {Ig} step = ⊥-elim (decI-Ig-noev step)

-- decI refuses tx / ack / output / rcvmsg / sndack at every position.
decI-no-tx : ∀ {i a W} →
  decI i ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-tx {I0} (sVis refl ())
decI-no-tx {I1} (sVis refl ())
decI-no-tx {I2} (sVis refl ())
decI-no-tx {Ig} step = decI-Ig-noev step

decI-no-ack : ∀ {i a W} →
  decI i ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-ack {I0} (sVis refl ())
decI-no-ack {I1} (sVis refl ())
decI-no-ack {I2} (sVis refl ())
decI-no-ack {Ig} step = decI-Ig-noev step

decI-no-output : ∀ {i a W} →
  decI i ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-output {I0} (sVis refl ())
decI-no-output {I1} (sVis refl ())
decI-no-output {I2} (sVis refl ())
decI-no-output {Ig} step = decI-Ig-noev step

decI-no-rcvmsg : ∀ {i a W} →
  decI i ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-rcvmsg {I0} (sVis refl ())
decI-no-rcvmsg {I1} (sVis refl ())
decI-no-rcvmsg {I2} (sVis refl ())
decI-no-rcvmsg {Ig} step = decI-Ig-noev step

decI-no-sndack : ∀ {i a W} →
  decI i ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-sndack {I0} (sVis refl ())
decI-no-sndack {I1} (sVis refl ())
decI-no-sndack {I2} (sVis refl ())
decI-no-sndack {Ig} step = decI-Ig-noev step

-- decT refuses input / ack / output / rcvmsg / sndack at every position.
decT-no-input : ∀ {t a W} →
  decT t ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-input {T0} (sVis refl ())
decT-no-input {T1} (sVis refl ())
decT-no-input {Tg} step = decT-Tg-noev step

decT-no-ack : ∀ {t a W} →
  decT t ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-ack {T0} (sVis refl ())
decT-no-ack {T1} (sVis refl ())
decT-no-ack {Tg} step = decT-Tg-noev step

decT-no-output : ∀ {t a W} →
  decT t ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-output {T0} (sVis refl ())
decT-no-output {T1} (sVis refl ())
decT-no-output {Tg} step = decT-Tg-noev step

decT-no-rcvmsg : ∀ {t a W} →
  decT t ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-rcvmsg {T0} (sVis refl ())
decT-no-rcvmsg {T1} (sVis refl ())
decT-no-rcvmsg {Tg} step = decT-Tg-noev step

decT-no-sndack : ∀ {t a W} →
  decT t ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-sndack {T0} (sVis refl ())
decT-no-sndack {T1} (sVis refl ())
decT-no-sndack {Tg} step = decT-Tg-noev step

-- decT offers `tx` only at T1 (→ Tg).
decT-tx-class : ∀ {t a W} →
  decT t ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → (t ≡ T1) × (W ≡ decT Tg)
decT-tx-class {T0} (sVis refl ())
decT-tx-class {T1} step = refl , decT-T1-tx step
decT-tx-class {Tg} step = ⊥-elim (decT-Tg-noev step)

-- decR refuses input / tx / output / rcvmsg / sndack at every position.
decR-no-input : ∀ {r a W} →
  decR r ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-input {R0} (sVis refl ())
decR-no-input {R1} (sVis refl ())
decR-no-input {Rg} step = decR-Rg-noev step

decR-no-tx : ∀ {r a W} →
  decR r ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-tx {R0} (sVis refl ())
decR-no-tx {R1} (sVis refl ())
decR-no-tx {Rg} step = decR-Rg-noev step

decR-no-output : ∀ {r a W} →
  decR r ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-output {R0} (sVis refl ())
decR-no-output {R1} (sVis refl ())
decR-no-output {Rg} step = decR-Rg-noev step

decR-no-rcvmsg : ∀ {r a W} →
  decR r ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-rcvmsg {R0} (sVis refl ())
decR-no-rcvmsg {R1} (sVis refl ())
decR-no-rcvmsg {Rg} step = decR-Rg-noev step

decR-no-sndack : ∀ {r a W} →
  decR r ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-sndack {R0} (sVis refl ())
decR-no-sndack {R1} (sVis refl ())
decR-no-sndack {Rg} step = decR-Rg-noev step

-- decR offers `ack` only at R0 (→ R1).
decR-ack-class : ∀ {r a W} →
  decR r ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → (r ≡ R0) × (W ≡ decR R1)
decR-ack-class {R0} step = refl , decR-R0-ack step
decR-ack-class {R1} (sVis refl ())
decR-ack-class {Rg} step = ⊥-elim (decR-Rg-noev step)

------------------------------------------------------------------------
-- TR-side visible-offer classifiers / refutations.
------------------------------------------------------------------------

-- TR offers `tx` only via decT at T1 (→ Tg); decR refuses tx ⇒ decT-solo.
TR-tx-class : ∀ {t r a W} →
  (decT t ⦀ decR r) ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W →
  (t ≡ T1) × (W ≡ (decT Tg ⦀ decR r))
TR-tx-class {t} {r} step
  with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = proj₁ cl , cong (λ z → z ⦀ decR r) (proj₂ cl)
  where cl = decT-tx-class {t} Tev
TR-tx-class {t} {r} step | evR  _ Rev = ⊥-elim (decR-no-tx {r} Rev)
TR-tx-class {t} {r} step | evBoth _ _ Rev = ⊥-elim (decR-no-tx {r} Rev)

-- TR offers `ack` only via decR at R0 (→ R1); decT refuses ack ⇒ decR-solo.
TR-ack-class : ∀ {t r a W} →
  (decT t ⦀ decR r) ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W →
  (r ≡ R0) × (W ≡ (decT t ⦀ decR R1))
TR-ack-class {t} {r} step
  with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = ⊥-elim (decT-no-ack {t} Tev)
TR-ack-class {t} {r} step | evR  _ Rev = proj₁ cl , cong (λ z → decT t ⦀ z) (proj₂ cl)
  where cl = decR-ack-class {r} Rev
TR-ack-class {t} {r} step | evBoth _ Tev _ = ⊥-elim (decT-no-ack {t} Tev)

-- TR refuses input / output / rcvmsg / sndack at every position.
TR-no-input : ∀ {t r a W} →
  (decT t ⦀ decR r) ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
TR-no-input {t} {r} step with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-input {t} Tev
... | evR  _ Rev       = decR-no-input {r} Rev
... | evBoth _ Tev _   = decT-no-input {t} Tev

TR-no-output : ∀ {t r a W} →
  (decT t ⦀ decR r) ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
TR-no-output {t} {r} step with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-output {t} Tev
... | evR  _ Rev       = decR-no-output {r} Rev
... | evBoth _ Tev _   = decT-no-output {t} Tev

TR-no-rcvmsg : ∀ {t r a W} →
  (decT t ⦀ decR r) ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
TR-no-rcvmsg {t} {r} step with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-rcvmsg {t} Tev
... | evR  _ Rev       = decR-no-rcvmsg {r} Rev
... | evBoth _ Tev _   = decT-no-rcvmsg {t} Tev

TR-no-sndack : ∀ {t r a W} →
  (decT t ⦀ decR r) ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
TR-no-sndack {t} {r} step with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-sndack {t} Tev
... | evR  _ Rev       = decR-no-sndack {r} Rev
... | evBoth _ Tev _   = decT-no-sndack {t} Tev

------------------------------------------------------------------------
-- sim-Tx-ev : characterise every VISIBLE offer of decTx i t r.
--   passing through the ∖ csSR' hide (event ∉ csSR', i.e. NOT sndmsg/rcvack):
--     · input  (i=I0)  → decTx I1 t r   (decI solo)
--     · tx     (t=T1)  → decTx i Tg r   (Transmitter emits; visible, ∉csSR')
--     · ack    (r=R0)  → decTx i t R1   (RcvAck accepts; visible, ∉csSR')
-- The event identity is pinned by a label-equality against the fixed
-- inputLbl / txLbl / ackLbl (M4c pattern-matches those).
------------------------------------------------------------------------

sim-Tx-ev : ∀ {i t r B} {e : Net ⊤ B} {a} {W} →
  decTx i t r ─[ ev (evl (evLabel B e a)) ]─► W →
    ((i ≡ I0) × (evl (evLabel B e a) ≡ inputLbl) × (W ≡ decTx I1 t r))
  ⊎ ((t ≡ T1) × (evl (evLabel B e a) ≡ txLbl)    × (W ≡ decTx i Tg r))
  ⊎ ((r ≡ R0) × (evl (evLabel B e a) ≡ ackLbl)   × (W ≡ decTx i t R1))
sim-Tx-ev {i} {t} {r} step
  with Hide-ev-elim csSR' (Par⊤ csSR' (decI i) (decT t ⦀ decR r)) step
... | heV {B} {e} {a} _ ¬cs parev with e
-- input: ∉csSR'; decI offers it solo at I0.
... | input N2N_ChainSync    ()
... | input N2N_BlockFetch   ()
... | input N2N_TxSubmission ()
... | input N2N_LeiosNotify  ()
... | input N2N_LeiosFetch   ()
... | input N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = inj₁ (proj₁ cl , refl ,
          cong (λ z → (Par⊤ csSR' z (decT t ⦀ decR r)) ∖ csSR') (proj₂ cl))
  where cl = decI-input-class {i} Iev
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | input N2N_KeepAlive zero
      | evR  _ TRev      = ⊥-elim (TR-no-input {t} {r} TRev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | input N2N_KeepAlive zero
      | evBoth _ _ TRev  = ⊥-elim (TR-no-input {t} {r} TRev)
-- tx: ∉csSR'; Transmitter emits it solo at T1.
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-tx {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      | evR  _ TRev      = inj₂ (inj₁ (proj₁ cl , refl ,
          cong (λ z → (Par⊤ csSR' (decI i) z) ∖ csSR') (proj₂ cl)))
  where cl = TR-tx-class {t} {r} TRev
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      | evBoth _ Iev _   = ⊥-elim (decI-no-tx {i} Iev)
-- ack: ∉csSR'; RcvAck accepts it solo at R0.
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-ack {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      | evR  _ TRev      = inj₂ (inj₂ (proj₁ cl , refl ,
          cong (λ z → (Par⊤ csSR' (decI i) z) ∖ csSR') (proj₂ cl)))
  where cl = TR-ack-class {t} {r} TRev
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      | evBoth _ Iev _   = ⊥-elim (decI-no-ack {i} Iev)
-- sndmsg / rcvack: ∈csSR', so the hide-passed `¬cs` is `¬ ⊤` ⇒ absurd.
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndmsg id c = ⊥-elim (¬cs Poly.tt)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvack id c = ⊥-elim (¬cs Poly.tt)
-- output / rcvmsg / sndack: neither decI nor TR offers them ⇒ refute.
-- (id-pinned via the IDs split, as for the sync events.)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-output {i} Iev)
...   | evR  _ TRev      = ⊥-elim (TR-no-output {t} {r} TRev)
...   | evBoth _ Iev _   = ⊥-elim (decI-no-output {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-rcvmsg {i} Iev)
...   | evR  _ TRev      = ⊥-elim (TR-no-rcvmsg {t} {r} TRev)
...   | evBoth _ Iev _   = ⊥-elim (decI-no-rcvmsg {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-sndack {i} Iev)
...   | evR  _ TRev      = ⊥-elim (TR-no-sndack {t} {r} TRev)
...   | evBoth _ Iev _   = ⊥-elim (decI-no-sndack {i} Iev)

------------------------------------------------------------------------
-- M4b: RxSide-level simulation lemmas (the MIRROR of M4a).
--
--   decRx o c s = (Par⊤ csRS' (decO o) (decC c ⦀ decS s)) ∖ csRS'
--
-- csRS' = {rcvmsg, sndack}.  RS = decC c ⦀ decS s  (mirror of TR).
--
-- Two deliverables for M4c:
--   sim-Rx-τ  : every τ of decRx is one of the 5 internal moves
--   sim-Rx-ev : every visible offer of decRx is one of output/tx/ack
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Operand-level τ classifiers (mirror decI/decT/decR-τ-class).
------------------------------------------------------------------------

decO-τ-class : ∀ {o W} → decO o ─[ τ ]─► W → (o ≡ Og) × (W ≡ decO O0)
decO-τ-class {O0} step = ⊥-elim (decO-O0-noτ step)
decO-τ-class {O1} step = ⊥-elim (decO-O1-noτ step)
decO-τ-class {O2} step = ⊥-elim (decO-O2-noτ step)
decO-τ-class {Og} step = refl , decO-Og-τ step

decC-τ-class : ∀ {c W} → decC c ─[ τ ]─► W → (c ≡ Rcg) × (W ≡ decC Rc0)
decC-τ-class {Rc0} step = ⊥-elim (decC-Rc0-noτ step)
decC-τ-class {Rc1} step = ⊥-elim (decC-Rc1-noτ step)
decC-τ-class {Rcg} step = refl , decC-Rcg-τ step

decS-τ-class : ∀ {s W} → decS s ─[ τ ]─► W → (s ≡ Sag) × (W ≡ decS Sa0)
decS-τ-class {Sa0} step = ⊥-elim (decS-Sa0-noτ step)
decS-τ-class {Sa1} step = ⊥-elim (decS-Sa1-noτ step)
decS-τ-class {Sag} step = refl , decS-Sag-τ step

------------------------------------------------------------------------
-- Operand-level event classifiers for the SYNC events (rcvmsg / sndack)
-- and the refutations that the partner operand refuses them.
------------------------------------------------------------------------

-- decO offers `rcvmsg` only at O0 (→ O1); refuse it at O1/O2/Og.
decO-rcvmsg-class : ∀ {o a W} →
  decO o ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → (o ≡ O0) × (W ≡ decO O1)
decO-rcvmsg-class {O0} step = refl , decO-O0-rcvmsg step
decO-rcvmsg-class {O1} (sVis refl ())
decO-rcvmsg-class {O2} (sVis refl ())
decO-rcvmsg-class {Og} step = ⊥-elim (decO-Og-noev step)

-- decO offers `sndack` only at O2 (→ Og); refuse it at O0/O1/Og.
decO-sndack-class : ∀ {o a W} →
  decO o ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → (o ≡ O2) × (W ≡ decO Og)
decO-sndack-class {O0} (sVis refl ())
decO-sndack-class {O1} (sVis refl ())
decO-sndack-class {O2} step = refl , decO-O2-sndack step
decO-sndack-class {Og} step = ⊥-elim (decO-Og-noev step)

-- decC (Receiver) offers `rcvmsg` only at Rc1 (→ Rcg); refuse it at Rc0/Rcg.
decC-rcvmsg-class : ∀ {c a W} →
  decC c ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → (c ≡ Rc1) × (W ≡ decC Rcg)
decC-rcvmsg-class {Rc0} (sVis refl ())
decC-rcvmsg-class {Rc1} step = refl , decC-Rc1-rcvmsg step
decC-rcvmsg-class {Rcg} step = ⊥-elim (decC-Rcg-noev step)

-- decC refuses `sndack` everywhere (it offers only tx / rcvmsg).
decC-no-sndack : ∀ {c a W} →
  decC c ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-sndack {Rc0} (sVis refl ())
decC-no-sndack {Rc1} (sVis refl ())
decC-no-sndack {Rcg} step = decC-Rcg-noev step

-- decS (SndAck) offers `sndack` only at Sa0 (→ Sa1); refuse it at Sa1/Sag.
decS-sndack-class : ∀ {s a W} →
  decS s ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → (s ≡ Sa0) × (W ≡ decS Sa1)
decS-sndack-class {Sa0} step = refl , decS-Sa0-sndack step
decS-sndack-class {Sa1} (sVis refl ())
decS-sndack-class {Sag} step = ⊥-elim (decS-Sag-noev step)

-- decS refuses `rcvmsg` everywhere (it offers only sndack / ack).
decS-no-rcvmsg : ∀ {s a W} →
  decS s ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-rcvmsg {Sa0} (sVis refl ())
decS-no-rcvmsg {Sa1} (sVis refl ())
decS-no-rcvmsg {Sag} step = decS-Sag-noev step

------------------------------------------------------------------------
-- RS = decC c ⦀ decS s  (the inner interleaving inside RxSide).
-- Classify its τ's and its rcvmsg/sndack syncs through `Par-ev/τ-elim ∅ES`.
------------------------------------------------------------------------

-- A τ of (decC c ⦀ decS s) is either decC's guard (c=Rcg, →Rc0) keeping decS,
-- or decS's guard (s=Sag, →Sa0) keeping decC.
RS-τ-class : ∀ {c s W} → (decC c ⦀ decS s) ─[ τ ]─► W →
    ((c ≡ Rcg) × (W ≡ (decC Rc0 ⦀ decS s)))
  ⊎ ((s ≡ Sag) × (W ≡ (decC c   ⦀ decS Sa0)))
RS-τ-class {c} {s} step with Par-τ-elim ∅ES ⊤merge (decC c) (decS s) step
... | τL P′ Cτ refl = inj₁ (proj₁ cl , cong (λ z → z ⦀ decS s) (proj₂ cl))
  where cl = decC-τ-class Cτ
... | τR Q′ Sτ refl = inj₂ (proj₁ cl , cong (λ z → decC c ⦀ z) (proj₂ cl))
  where cl = decS-τ-class Sτ

-- The rcvmsg sync of RS: decC accepts (Rc1→Rcg); decS refuses ⇒ decC-solo.
RS-rcvmsg-class : ∀ {c s a W} →
  (decC c ⦀ decS s) ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W →
  (c ≡ Rc1) × (W ≡ (decC Rcg ⦀ decS s))
RS-rcvmsg-class {c} {s} step
  with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = proj₁ cl , cong (λ z → z ⦀ decS s) (proj₂ cl)
  where cl = decC-rcvmsg-class {c} Cev
RS-rcvmsg-class {c} {s} step | evR  _ Sev = ⊥-elim (decS-no-rcvmsg {s} Sev)
RS-rcvmsg-class {c} {s} step | evBoth _ Cev Sev = ⊥-elim (decS-no-rcvmsg {s} Sev)

-- The sndack sync of RS: decS offers (Sa0→Sa1); decC refuses ⇒ decS-solo.
RS-sndack-class : ∀ {c s a W} →
  (decC c ⦀ decS s) ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W →
  (s ≡ Sa0) × (W ≡ (decC c ⦀ decS Sa1))
RS-sndack-class {c} {s} step
  with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = ⊥-elim (decC-no-sndack {c} Cev)
RS-sndack-class {c} {s} step | evR  _ Sev = proj₁ cl , cong (λ z → decC c ⦀ z) (proj₂ cl)
  where cl = decS-sndack-class {s} Sev
RS-sndack-class {c} {s} step | evBoth _ Cev _ = ⊥-elim (decC-no-sndack {c} Cev)

------------------------------------------------------------------------
-- sim-Rx-τ : characterise every τ of decRx o c s.
--   internal moves: rcvmsg-sync, sndack-sync, guard gO, guard gRc, guard gSa.
------------------------------------------------------------------------

sim-Rx-τ : ∀ {o c s W} → decRx o c s ─[ τ ]─► W →
    ((c ≡ Rc1) × (o ≡ O0) × (W ≡ decRx O1 Rcg s))   -- rcvmsg sync
  ⊎ ((o ≡ O2) × (s ≡ Sa0) × (W ≡ decRx Og c Sa1))    -- sndack sync
  ⊎ ((o ≡ Og) × (W ≡ decRx O0 c s))                  -- gO
  ⊎ ((c ≡ Rcg) × (W ≡ decRx o Rc0 s))                -- gRc
  ⊎ ((s ≡ Sag) × (W ≡ decRx o c Sa0))                -- gSa
sim-Rx-τ {o} {c} {s} step
  with Hide-τ-elim csRS' (Par⊤ csRS' (decO o) (decC c ⦀ decS s)) step
-- (A) the inner Par's own τ: decO guard, or a τ of RS (decC/decS guard).
... | hτP _ parτ refl
      with Par-τ-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parτ
...   | τL _ Oτ refl =
        inj₂ (inj₂ (inj₁ (proj₁ cl ,
          cong (λ z → (Par⊤ csRS' z (decC c ⦀ decS s)) ∖ csRS') (proj₂ cl))))
  where cl = decO-τ-class Oτ
sim-Rx-τ {o} {c} {s} step | hτP _ parτ refl
      | τR _ RSτ refl with RS-τ-class RSτ
...     | inj₁ (gc , weq) =
          inj₂ (inj₂ (inj₂ (inj₁ (gc ,
            cong (λ z → (Par⊤ csRS' (decO o) z) ∖ csRS') weq))))
...     | inj₂ (gs , weq) =
          inj₂ (inj₂ (inj₂ (inj₂ (gs ,
            cong (λ z → (Par⊤ csRS' (decO o) z) ∖ csRS') weq))))
-- (B) a HIDDEN csRS-event of the inner Par: a rcvmsg or sndack SYNC.
sim-Rx-τ {o} {c} {s} step
  | hτH {B} {e} {a} _ mem parev refl with e
-- rcvmsg sync: pin id/c, then classify.
... | rcvmsg N2N_ChainSync    ()
... | rcvmsg N2N_BlockFetch   ()
... | rcvmsg N2N_TxSubmission ()
... | rcvmsg N2N_LeiosNotify  ()
... | rcvmsg N2N_LeiosFetch   ()
... | rcvmsg N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync _ Oev RSev = inj₁ (proj₁ clRS , proj₁ clO ,
          cong₂ (λ z w → (Par⊤ csRS' z w) ∖ csRS') (proj₂ clO) (proj₂ clRS))
  where clO  = decO-rcvmsg-class {o} Oev
        clRS = RS-rcvmsg-class {c} {s} RSev
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg N2N_KeepAlive zero
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg N2N_KeepAlive zero
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg N2N_KeepAlive zero
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
-- sndack sync: same id/c pinning.
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_ChainSync    ()
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_BlockFetch   ()
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_TxSubmission ()
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_LeiosNotify  ()
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_LeiosFetch   ()
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync _ Oev RSev = inj₂ (inj₁ (proj₁ clO , proj₁ clRS ,
          cong₂ (λ z w → (Par⊤ csRS' z w) ∖ csRS') (proj₂ clO) (proj₂ clRS)))
  where clO  = decO-sndack-class {o} Oev
        clRS = RS-sndack-class {c} {s} RSev
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_KeepAlive zero
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_KeepAlive zero
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_KeepAlive zero
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
-- non-csRS constructors: `mem : csRS' .mem (B,e) a = ⊥`.
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | input id c′  = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | output id c′ = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | tx id c′     = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndmsg id c′ = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvack id c′ = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | ack id c′    = ⊥-elim mem

------------------------------------------------------------------------
-- Operand-level visible-offer classifiers / refutations for the NON-csRS
-- events (output on decO; tx / ack on the RS side).  Fixed at the channel
-- `N2N_KeepAlive c0`; id-pinning is done at the sim-Rx-ev call site.
------------------------------------------------------------------------

-- decO offers `output` only at O1 (→ O2).
decO-output-class : ∀ {o a W} →
  decO o ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → (o ≡ O1) × (W ≡ decO O2)
decO-output-class {O0} (sVis refl ())
decO-output-class {O1} step = refl , decO-O1-output step
decO-output-class {O2} (sVis refl ())
decO-output-class {Og} step = ⊥-elim (decO-Og-noev step)

-- decO refuses tx / ack / input / sndmsg / rcvack at every position.
decO-no-tx : ∀ {o a W} →
  decO o ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-tx {O0} (sVis refl ())
decO-no-tx {O1} (sVis refl ())
decO-no-tx {O2} (sVis refl ())
decO-no-tx {Og} step = decO-Og-noev step

decO-no-ack : ∀ {o a W} →
  decO o ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-ack {O0} (sVis refl ())
decO-no-ack {O1} (sVis refl ())
decO-no-ack {O2} (sVis refl ())
decO-no-ack {Og} step = decO-Og-noev step

decO-no-input : ∀ {o a W} →
  decO o ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-input {O0} (sVis refl ())
decO-no-input {O1} (sVis refl ())
decO-no-input {O2} (sVis refl ())
decO-no-input {Og} step = decO-Og-noev step

decO-no-sndmsg : ∀ {o a W} →
  decO o ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-sndmsg {O0} (sVis refl ())
decO-no-sndmsg {O1} (sVis refl ())
decO-no-sndmsg {O2} (sVis refl ())
decO-no-sndmsg {Og} step = decO-Og-noev step

decO-no-rcvack : ∀ {o a W} →
  decO o ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-rcvack {O0} (sVis refl ())
decO-no-rcvack {O1} (sVis refl ())
decO-no-rcvack {O2} (sVis refl ())
decO-no-rcvack {Og} step = decO-Og-noev step

-- decC (Receiver) offers `tx` only at Rc0 (→ Rc1).
decC-tx-class : ∀ {c a W} →
  decC c ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → (c ≡ Rc0) × (W ≡ decC Rc1)
decC-tx-class {Rc0} step = refl , decC-Rc0-tx step
decC-tx-class {Rc1} (sVis refl ())
decC-tx-class {Rcg} step = ⊥-elim (decC-Rcg-noev step)

-- decC refuses output / ack / input / sndmsg / rcvack at every position.
decC-no-output : ∀ {c a W} →
  decC c ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-output {Rc0} (sVis refl ())
decC-no-output {Rc1} (sVis refl ())
decC-no-output {Rcg} step = decC-Rcg-noev step

decC-no-ack : ∀ {c a W} →
  decC c ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-ack {Rc0} (sVis refl ())
decC-no-ack {Rc1} (sVis refl ())
decC-no-ack {Rcg} step = decC-Rcg-noev step

decC-no-input : ∀ {c a W} →
  decC c ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-input {Rc0} (sVis refl ())
decC-no-input {Rc1} (sVis refl ())
decC-no-input {Rcg} step = decC-Rcg-noev step

decC-no-sndmsg : ∀ {c a W} →
  decC c ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-sndmsg {Rc0} (sVis refl ())
decC-no-sndmsg {Rc1} (sVis refl ())
decC-no-sndmsg {Rcg} step = decC-Rcg-noev step

decC-no-rcvack : ∀ {c a W} →
  decC c ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-rcvack {Rc0} (sVis refl ())
decC-no-rcvack {Rc1} (sVis refl ())
decC-no-rcvack {Rcg} step = decC-Rcg-noev step

-- decS (SndAck) offers `ack` only at Sa1 (→ Sag).
decS-ack-class : ∀ {s a W} →
  decS s ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → (s ≡ Sa1) × (W ≡ decS Sag)
decS-ack-class {Sa0} (sVis refl ())
decS-ack-class {Sa1} step = refl , decS-Sa1-ack step
decS-ack-class {Sag} step = ⊥-elim (decS-Sag-noev step)

-- decS refuses output / tx / input / sndmsg / rcvack at every position.
decS-no-output : ∀ {s a W} →
  decS s ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-output {Sa0} (sVis refl ())
decS-no-output {Sa1} (sVis refl ())
decS-no-output {Sag} step = decS-Sag-noev step

decS-no-tx : ∀ {s a W} →
  decS s ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-tx {Sa0} (sVis refl ())
decS-no-tx {Sa1} (sVis refl ())
decS-no-tx {Sag} step = decS-Sag-noev step

decS-no-input : ∀ {s a W} →
  decS s ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-input {Sa0} (sVis refl ())
decS-no-input {Sa1} (sVis refl ())
decS-no-input {Sag} step = decS-Sag-noev step

decS-no-sndmsg : ∀ {s a W} →
  decS s ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-sndmsg {Sa0} (sVis refl ())
decS-no-sndmsg {Sa1} (sVis refl ())
decS-no-sndmsg {Sag} step = decS-Sag-noev step

decS-no-rcvack : ∀ {s a W} →
  decS s ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-rcvack {Sa0} (sVis refl ())
decS-no-rcvack {Sa1} (sVis refl ())
decS-no-rcvack {Sag} step = decS-Sag-noev step

------------------------------------------------------------------------
-- RS-side visible-offer classifiers / refutations.
------------------------------------------------------------------------

-- RS offers `tx` only via decC at Rc0 (→ Rc1); decS refuses tx ⇒ decC-solo.
RS-tx-class : ∀ {c s a W} →
  (decC c ⦀ decS s) ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W →
  (c ≡ Rc0) × (W ≡ (decC Rc1 ⦀ decS s))
RS-tx-class {c} {s} step
  with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = proj₁ cl , cong (λ z → z ⦀ decS s) (proj₂ cl)
  where cl = decC-tx-class {c} Cev
RS-tx-class {c} {s} step | evR  _ Sev = ⊥-elim (decS-no-tx {s} Sev)
RS-tx-class {c} {s} step | evBoth _ _ Sev = ⊥-elim (decS-no-tx {s} Sev)

-- RS offers `ack` only via decS at Sa1 (→ Sag); decC refuses ack ⇒ decS-solo.
RS-ack-class : ∀ {c s a W} →
  (decC c ⦀ decS s) ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W →
  (s ≡ Sa1) × (W ≡ (decC c ⦀ decS Sag))
RS-ack-class {c} {s} step
  with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = ⊥-elim (decC-no-ack {c} Cev)
RS-ack-class {c} {s} step | evR  _ Sev = proj₁ cl , cong (λ z → decC c ⦀ z) (proj₂ cl)
  where cl = decS-ack-class {s} Sev
RS-ack-class {c} {s} step | evBoth _ Cev _ = ⊥-elim (decC-no-ack {c} Cev)

-- RS refuses output / input / sndmsg / rcvack at every position.
RS-no-output : ∀ {c s a W} →
  (decC c ⦀ decS s) ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
RS-no-output {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-output {c} Cev
... | evR  _ Sev       = decS-no-output {s} Sev
... | evBoth _ Cev _   = decC-no-output {c} Cev

RS-no-input : ∀ {c s a W} →
  (decC c ⦀ decS s) ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
RS-no-input {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-input {c} Cev
... | evR  _ Sev       = decS-no-input {s} Sev
... | evBoth _ Cev _   = decC-no-input {c} Cev

RS-no-sndmsg : ∀ {c s a W} →
  (decC c ⦀ decS s) ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
RS-no-sndmsg {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-sndmsg {c} Cev
... | evR  _ Sev       = decS-no-sndmsg {s} Sev
... | evBoth _ Cev _   = decC-no-sndmsg {c} Cev

RS-no-rcvack : ∀ {c s a W} →
  (decC c ⦀ decS s) ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
RS-no-rcvack {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-rcvack {c} Cev
... | evR  _ Sev       = decS-no-rcvack {s} Sev
... | evBoth _ Cev _   = decC-no-rcvack {c} Cev

------------------------------------------------------------------------
-- sim-Rx-ev : characterise every VISIBLE offer of decRx o c s.
--   passing through the ∖ csRS' hide (event ∉ csRS', i.e. NOT rcvmsg/sndack):
--     · output (o=O1)  → decRx O2 c s   (decO solo)
--     · tx     (c=Rc0) → decRx o Rc1 s  (Receiver accepts; visible, ∉csRS')
--     · ack    (s=Sa1) → decRx o c Sag  (SndAck emits; visible, ∉csRS')
-- The event identity is pinned by a label-equality against the fixed
-- outputLbl / txLbl / ackLbl (M4c pattern-matches those).
------------------------------------------------------------------------

sim-Rx-ev : ∀ {o c s B} {e : Net ⊤ B} {a} {W} →
  decRx o c s ─[ ev (evl (evLabel B e a)) ]─► W →
    ((o ≡ O1)  × (evl (evLabel B e a) ≡ outputLbl) × (W ≡ decRx O2 c s))
  ⊎ ((c ≡ Rc0) × (evl (evLabel B e a) ≡ txLbl)     × (W ≡ decRx o Rc1 s))
  ⊎ ((s ≡ Sa1) × (evl (evLabel B e a) ≡ ackLbl)    × (W ≡ decRx o c Sag))
sim-Rx-ev {o} {c} {s} step
  with Hide-ev-elim csRS' (Par⊤ csRS' (decO o) (decC c ⦀ decS s)) step
... | heV {B} {e} {a} _ ¬cs parev with e
-- output: ∉csRS'; decO offers it solo at O1.
... | output N2N_ChainSync    ()
... | output N2N_BlockFetch   ()
... | output N2N_TxSubmission ()
... | output N2N_LeiosNotify  ()
... | output N2N_LeiosFetch   ()
... | output N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = inj₁ (proj₁ cl , refl ,
          cong (λ z → (Par⊤ csRS' z (decC c ⦀ decS s)) ∖ csRS') (proj₂ cl))
  where cl = decO-output-class {o} Oev
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | output N2N_KeepAlive zero
      | evR  _ RSev      = ⊥-elim (RS-no-output {c} {s} RSev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | output N2N_KeepAlive zero
      | evBoth _ _ RSev  = ⊥-elim (RS-no-output {c} {s} RSev)
-- tx: ∉csRS'; Receiver accepts it solo at Rc0.
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-tx {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      | evR  _ RSev      = inj₂ (inj₁ (proj₁ cl , refl ,
          cong (λ z → (Par⊤ csRS' (decO o) z) ∖ csRS') (proj₂ cl)))
  where cl = RS-tx-class {c} {s} RSev
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      | evBoth _ Oev _   = ⊥-elim (decO-no-tx {o} Oev)
-- ack: ∉csRS'; SndAck emits it solo at Sa1.
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-ack {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      | evR  _ RSev      = inj₂ (inj₂ (proj₁ cl , refl ,
          cong (λ z → (Par⊤ csRS' (decO o) z) ∖ csRS') (proj₂ cl)))
  where cl = RS-ack-class {c} {s} RSev
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      | evBoth _ Oev _   = ⊥-elim (decO-no-ack {o} Oev)
-- rcvmsg / sndack: ∈csRS', so the hide-passed `¬cs` is `¬ ⊤` ⇒ absurd.
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg id c′ = ⊥-elim (¬cs Poly.tt)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndack id c′ = ⊥-elim (¬cs Poly.tt)
-- input / sndmsg / rcvack: neither decO nor RS offers them ⇒ refute.
-- (id-pinned via the IDs split, as for the sync events.)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-input {o} Oev)
...   | evR  _ RSev      = ⊥-elim (RS-no-input {c} {s} RSev)
...   | evBoth _ Oev _   = ⊥-elim (decO-no-input {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-sndmsg {o} Oev)
...   | evR  _ RSev      = ⊥-elim (RS-no-sndmsg {c} {s} RSev)
...   | evBoth _ Oev _   = ⊥-elim (decO-no-sndmsg {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-rcvack {o} Oev)
...   | evR  _ RSev      = ⊥-elim (RS-no-rcvack {c} {s} RSev)
...   | evBoth _ Oev _   = ⊥-elim (decO-no-rcvack {o} Oev)


------------------------------------------------------------------------
-- M4c: TOP-LEVEL simulation through `Par⊤ csTA'`.
--
-- `⟦ mkCS i t r o c s ⟧ = Par⊤ csTA' (decTx i t r) (decRx o c s)`.
-- Glue the four side lemmas (sim-Tx-τ / sim-Tx-ev / sim-Rx-τ / sim-Rx-ev)
-- through the top `Par⊤ csTA'`:
--   sim-modA : every modulo-csTA step is an internal `_⇒ᵢ_` move;
--   sim-uVis : every NON-csTA visible offer is a `_⇒ᵥ_` move (input/output).
------------------------------------------------------------------------

-- Label-disequalities: the four visible/sync labels are pairwise distinct.
inputLbl≢outputLbl : inputLbl ≡ outputLbl → ⊥
inputLbl≢outputLbl ()
inputLbl≢txLbl : inputLbl ≡ txLbl → ⊥
inputLbl≢txLbl ()
inputLbl≢ackLbl : inputLbl ≡ ackLbl → ⊥
inputLbl≢ackLbl ()
outputLbl≢txLbl : outputLbl ≡ txLbl → ⊥
outputLbl≢txLbl ()
outputLbl≢ackLbl : outputLbl ≡ ackLbl → ⊥
outputLbl≢ackLbl ()
txLbl≢ackLbl : txLbl ≡ ackLbl → ⊥
txLbl≢ackLbl ()

-- From a label equality identifying the carried event with `tx`/`ack`/`input`/
-- `output`, build the csTA membership (so a `¬cs`-refusal can be contradicted).
txLbl→mem : ∀ {B} {e : Net ⊤ B} {a}
          → evl (evLabel B e a) ≡ txLbl → csTA' .mem (B , e) a
txLbl→mem refl = Poly.tt
ackLbl→mem : ∀ {B} {e : Net ⊤ B} {a}
           → evl (evLabel B e a) ≡ ackLbl → csTA' .mem (B , e) a
ackLbl→mem refl = Poly.tt

------------------------------------------------------------------------
-- sim-modA : every modulo-csTA step of ⟦ cs ⟧ is an internal `_⇒ᵢ_` move.
------------------------------------------------------------------------

sim-modA : ∀ cs {W′} → ModAStep csTA' ⟦ cs ⟧ W′
         → Σ[ cs′ ∈ CS ] ((cs ⇒ᵢ cs′) × (W′ ≡ ⟦ cs′ ⟧))
-- (1) a τ of the inner Par: either a Tx-side τ or an Rx-side τ.
sim-modA (mkCS i t r o c s) (maτ parτ)
  with Par-τ-elim csTA' ⊤merge (decTx i t r) (decRx o c s) parτ
... | τL P′ Txτ refl with sim-Tx-τ {i} {t} {r} Txτ
...   | inj₁ (refl , refl , Weq) =
        mkCS I2 T1 r o c s , NM.sndmsg ,
        cong (λ z → Par⊤ csTA' z (decRx o c s)) Weq
...   | inj₂ (inj₁ (refl , refl , Weq)) =
        mkCS Ig t Rg o c s , NM.rcvack ,
        cong (λ z → Par⊤ csTA' z (decRx o c s)) Weq
...   | inj₂ (inj₂ (inj₁ (refl , Weq))) =
        mkCS I0 t r o c s , gI ,
        cong (λ z → Par⊤ csTA' z (decRx o c s)) Weq
...   | inj₂ (inj₂ (inj₂ (inj₁ (refl , Weq)))) =
        mkCS i T0 r o c s , gT ,
        cong (λ z → Par⊤ csTA' z (decRx o c s)) Weq
...   | inj₂ (inj₂ (inj₂ (inj₂ (refl , Weq)))) =
        mkCS i t R0 o c s , gR ,
        cong (λ z → Par⊤ csTA' z (decRx o c s)) Weq
sim-modA (mkCS i t r o c s) (maτ parτ)
  | τR Q′ Rxτ refl with sim-Rx-τ {o} {c} {s} Rxτ
...   | inj₁ (refl , refl , Weq) =
        mkCS i t r O1 Rcg s , NM.rcvmsg ,
        cong (λ z → Par⊤ csTA' (decTx i t r) z) Weq
...   | inj₂ (inj₁ (refl , refl , Weq)) =
        mkCS i t r Og c Sa1 , NM.sndack ,
        cong (λ z → Par⊤ csTA' (decTx i t r) z) Weq
...   | inj₂ (inj₂ (inj₁ (refl , Weq))) =
        mkCS i t r O0 c s , gO ,
        cong (λ z → Par⊤ csTA' (decTx i t r) z) Weq
...   | inj₂ (inj₂ (inj₂ (inj₁ (refl , Weq)))) =
        mkCS i t r o Rc0 s , gRc ,
        cong (λ z → Par⊤ csTA' (decTx i t r) z) Weq
...   | inj₂ (inj₂ (inj₂ (inj₂ (refl , Weq)))) =
        mkCS i t r o c Sa0 , gSa ,
        cong (λ z → Par⊤ csTA' (decTx i t r) z) Weq
-- (2) a hidden csTA-event (tx/ack): a SYNC between Tx- and Rx-sides.
--   The non-sync eliminations (evL/evR/evBoth) carry `¬cs` contradicting `mem`.
sim-modA (mkCS i t r o c s) (maE mem parev)
  with Par-ev-elim csTA' ⊤merge (decTx i t r) (decRx o c s) parev
... | evL  ¬cs _   = ⊥-elim (¬cs mem)
... | evR  ¬cs _   = ⊥-elim (¬cs mem)
... | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
... | evSync _ Txev Rxev with sim-Tx-ev {i} {t} {r} Txev | sim-Rx-ev {o} {c} {s} Rxev
-- Tx = input (∉csTA): the shared label can be neither output/tx/ack.
...   | inj₁ (_ , Lin , _) | inj₁ (_ , Lout , _) =
          ⊥-elim (inputLbl≢outputLbl (trans (sym Lin) Lout))
...   | inj₁ (_ , Lin , _) | inj₂ (inj₁ (_ , Ltx , _)) =
          ⊥-elim (inputLbl≢txLbl (trans (sym Lin) Ltx))
...   | inj₁ (_ , Lin , _) | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (inputLbl≢ackLbl (trans (sym Lin) Lack))
-- Tx = tx: consistent only with Rx = tx ⇒ `⇒ᵢ tx`.
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₁ (_ , Lout , _) =
          ⊥-elim (outputLbl≢txLbl (trans (sym Lout) Ltx))
...   | inj₂ (inj₁ (refl , _ , refl)) | inj₂ (inj₁ (refl , _ , refl)) =
          mkCS i Tg r o Rc1 s , NM.tx , refl
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (txLbl≢ackLbl (trans (sym Ltx) Lack))
-- Tx = ack: consistent only with Rx = ack ⇒ `⇒ᵢ ack`.
...   | inj₂ (inj₂ (refl , Lack , refl)) | inj₁ (_ , Lout , _) =
          ⊥-elim (outputLbl≢ackLbl (trans (sym Lout) Lack))
...   | inj₂ (inj₂ (refl , Lack , refl)) | inj₂ (inj₁ (_ , Ltx , _)) =
          ⊥-elim (txLbl≢ackLbl (trans (sym Ltx) Lack))
...   | inj₂ (inj₂ (refl , _ , refl)) | inj₂ (inj₂ (refl , _ , refl)) =
          mkCS i t R1 o c Sag , NM.ack , refl

------------------------------------------------------------------------
-- sim-uVis : every NON-csTA visible offer of ⟦ cs ⟧ is a `_⇒ᵥ_` move.
--   The only non-csTA visible events are `input` (Tx-side, solo) and
--   `output` (Rx-side, solo); the tx/ack disjuncts of the side lemmas are
--   in csTA', contradicting the `¬cs` hypothesis.
------------------------------------------------------------------------

sim-uVis : ∀ cs {B} {e : Net ⊤ B} {a} {W′}
         → ¬ csTA' .mem (B , e) a
         → ⟦ cs ⟧ ─[ ev (evl (evLabel B e a)) ]─► W′
         → Σ[ cs′ ∈ CS ] ((cs ⇒ᵥ cs′) × (W′ ≡ ⟦ cs′ ⟧))
sim-uVis (mkCS i t r o c s) ¬cs st
  with Par-ev-elim csTA' ⊤merge (decTx i t r) (decRx o c s) st
-- a SOLO Tx-side offer (∉csTA): must be `input` (tx/ack would be in csTA').
... | evL _ Txev with sim-Tx-ev {i} {t} {r} Txev
...   | inj₁ (refl , _ , Weq) =
        mkCS I1 t r o c s , NM.input ,
        cong (λ z → Par⊤ csTA' z (decRx o c s)) Weq
...   | inj₂ (inj₁ (_ , Ltx  , _)) = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) = ⊥-elim (¬cs (ackLbl→mem Lack))
-- a SOLO Rx-side offer (∉csTA): must be `output`.
sim-uVis (mkCS i t r o c s) ¬cs st
  | evR _ Rxev with sim-Rx-ev {o} {c} {s} Rxev
...   | inj₁ (refl , _ , Weq) =
        mkCS i t r O2 c s , NM.output ,
        cong (λ z → Par⊤ csTA' (decTx i t r) z) Weq
...   | inj₂ (inj₁ (_ , Ltx  , _)) = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) = ⊥-elim (¬cs (ackLbl→mem Lack))
-- a SYNC: the synced event is in csTA', contradicting `¬cs`.
sim-uVis (mkCS i t r o c s) ¬cs st | evSync mem _ _ = ⊥-elim (¬cs mem)
-- both-solo (∉csTA): Tx can only offer `input`, Rx only `output`;
--   their shared label can't be both ⇒ ⊥ (and tx/ack contradict `¬cs`).
sim-uVis (mkCS i t r o c s) ¬cs st
  | evBoth _ Txev Rxev with sim-Tx-ev {i} {t} {r} Txev | sim-Rx-ev {o} {c} {s} Rxev
...   | inj₁ (_ , Lin , _)        | inj₁ (_ , Lout , _) =
          ⊥-elim (inputLbl≢outputLbl (trans (sym Lin) Lout))
...   | inj₁ (_ , Lin , _)        | inj₂ (inj₁ (_ , Ltx , _)) =
          ⊥-elim (inputLbl≢txLbl (trans (sym Lin) Ltx))
...   | inj₁ (_ , Lin , _)        | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (inputLbl≢ackLbl (trans (sym Lin) Lack))
...   | inj₂ (inj₁ (_ , Ltx , _)) | _ = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) | _ = ⊥-elim (¬cs (ackLbl→mem Lack))

------------------------------------------------------------------------
-- MILESTONE 2 RESULT: `CopySpec ⊑D Network`, postulate-free.
--
-- We assemble the divergence refinement from the finite-state abstraction
-- `NetModel`:
--   * `MAcc-cs`  — every decoded state `⟦ cs ⟧` is modulo-csTA accessible,
--     by well-founded recursion on the measure `μ cs` (each `_⇒ᵢ_` edge
--     strictly decreases `μ`, via `μ-dec`);
--   * `goodU-cs` — the coinductive `GoodU` invariant holds at every `⟦ cs ⟧`
--     (corecursion guarded under `.gstep`, walking `sim-modA`/`sim-uVis`);
--   * `goodU-T0` — instantiated at `cs0` (`⟦ cs0 ⟧ ≡ T` by `dec-cs0`);
--   * `Reach-noDiv` then shows no weakly-reachable state of `Network`
--     diverges, so `divergences Network` is empty and the inclusion is
--     vacuous.
------------------------------------------------------------------------

open import Data.Nat using (_<_)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Relation.Binary.PropositionalEquality using (subst)

-- (1) Measure-based MAcc: well-founded recursion on `μ cs`.
MAcc-cs-acc : ∀ cs → Acc _<_ (NM.μ cs) → MAcc csTA' ⟦ cs ⟧
MAcc-cs-acc cs (acc rs) = macc λ {W′} step →
  let (cs′ , red , Weq) = sim-modA cs step
  in subst (MAcc csTA') (sym Weq) (MAcc-cs-acc cs′ (rs (NM.μ-dec red)))

MAcc-cs : ∀ cs → MAcc csTA' ⟦ cs ⟧
MAcc-cs cs = MAcc-cs-acc cs (<-wellFounded (NM.μ cs))

-- (2) The coinductive `GoodU` invariant at every decoded state.
--   `gmacc` is `MAcc-cs`; `gstep` walks `sim-modA` / `sim-uVis` to the next
--   `⟦ cs′ ⟧` and corecurses (guarded under the `.gstep` projection).
-- guarded helper: with `Weq : W′ ≡ ⟦ cs′ ⟧` matched to `refl`, the goal type
-- becomes `GoodU ⟦ cs′ ⟧` definitionally, so the corecursive `goodU-cs cs′`
-- stays directly under the `.gstep` copattern (productive, no `subst`).
goodU-cs   : ∀ cs → GoodU ⟦ cs ⟧
goodU-next : ∀ {W′} {R : CS → Set} → Σ[ cs′ ∈ CS ] (R cs′ × (W′ ≡ ⟦ cs′ ⟧)) → GoodU W′

goodU-cs cs .gmacc = MAcc-cs cs
goodU-cs cs .gstep (uMod step)     = goodU-next (sim-modA cs step)
goodU-cs cs .gstep (uVis ¬cs step) = goodU-next (sim-uVis cs ¬cs step)

goodU-next (cs′ , _ , refl) = goodU-cs cs′

-- (3) `GoodU` at the initial composite `T` (= `⟦ cs0 ⟧` by `dec-cs0`).
goodU-T0 : GoodU T
goodU-T0 = subst GoodU dec-cs0 (goodU-cs cs0)

-- The divergence refinement.  `Network = T ∖ csTA'` definitionally, so the
-- divergence witness's reach is a weak run out of `T ∖ csTA'`; `Reach-noDiv`
-- says it cannot reach a divergent state, refuting `divwit`.
CopySpec⊑D-Network : CopySpec ⊑D Network
CopySpec⊑D-Network div =
  ⊥-elim (Reach-noDiv goodU-T0 (IsDivergence.reach div) (IsDivergence.divwit div))

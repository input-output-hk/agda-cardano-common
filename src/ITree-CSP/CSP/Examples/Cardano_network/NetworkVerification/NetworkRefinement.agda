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
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import Data.List using (_∷_; [])
open import CSP.Examples.Cardano_network.Base using
  ( IDs; Dir; lo; hi; N2N_KeepAlive
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
  ; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetModel
  using ( CS; mkCS; cs0
        ; inp; tr; ra; out; rc; sa
        ; IP; I0; I1; I2; Ig
        ; TP; T0; T1; Tg
        ; RP; R0; R1; Rg
        ; OP; O0; O1; O2; Og
        ; CP; Rc0; Rc1; Rcg
        ; SP; Sa0; Sa1; Sag
        ; _⇒ᵢ_; _⇒ᵥ_
        ; gI; gT; gR; gO; gRc; gSa )
import CSP.Examples.Cardano_network.NetModel as NM

module CSP.Examples.Cardano_network.NetworkVerification.NetworkRefinement where

open PTree
open ExtI

------------------------------------------------------------------------
-- The single-channel instance.
------------------------------------------------------------------------

instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

import Data.Maybe as PMaybe

p1 : Params
p1 = record
  { Cookie = ⊤ ; Block = ⊤ ; Txid = ⊤ ; LSlot = ⊤
  ; VoterId = ⊤ ; LFBitmap = ⊤ ; VoteBlob = ⊤
  ; numLinks = 1
  ; linkConfig = λ _ → (lo , N2N_KeepAlive) ∷ []
  ; decCookie  = decEq⊤ ; decBlock    = decEq⊤ ; decTxid    = decEq⊤
  ; decLSlot   = decEq⊤ ; decVoterId  = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤
  ; Time = ⊤ ; Length = ⊤ ; time₀ = tt ; length₀ = tt
  ; decTime = decEq⊤ ; decLength = decEq⊤
  -- Leios EB domains, inert here: both ⊤, no RB ever announces an EB
  ; EB = ⊤ ; EBHash = ⊤ ; decEB = decEq⊤ ; decEBHash = decEq⊤
  ; ebHash = λ _ → tt ; announcedEB = λ _ → PMaybe.nothing }

open import CSP.Examples.Cardano_network.Net p1
  using (Net; Link; input; output; sndmsg; tx)
open import CSP.Examples.Cardano_network.Network p1 ⊤

open import Semantics.LTS {E = Net ⊤} {I = ExtI (Net ⊤)} hiding (Diverges)
open import Semantics.WeakBisim {E = Net ⊤} {I = ExtI (Net ⊤)}
open import Semantics.DRBisim {E = Net ⊤} {I = ExtI (Net ⊤)}
  using (Diverges; _≈DR_; deadlock-converges; drbisim→wbisim; drbisim-sym)
open import Semantics.Failures {E = Net ⊤} {I = ExtI (Net ⊤)}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces-respects-≈)
open import Semantics.FailuresDivergences {E = Net ⊤} {I = ExtI (Net ⊤)}
  using (_⊑D_; divergences; IsDivergence; _⊑F⊥_; _⊑FD_; _≈FD_)
open import Semantics.DRImpliesFD {E = Net ⊤} {I = ExtI (Net ⊤)}
  using (drbisim→≈FD)
open import Semantics.Expansion {E = Net ⊤} {I = ExtI (Net ⊤)}
  using (Expand; ExpBwdF; _⪰_; ⪯→≈DR)

-- the Net-decidable-equality used to instantiate every law module
open import CSP.Examples.Cardano_network.Net p1 using (Net-≟)

open import CSP.Operators {E = Net ⊤} (Net-≟ {⊤})
  using (Par⊤; _∥⇘_⇙_; _⦀_; _∖_; chanSet; ∅ES; EventSet; Skip; Par; viewV)
open EventSet

⊤merge : Poly.⊤ {0ℓ} → Poly.⊤ {0ℓ} → Poly.⊤ {0ℓ}
⊤merge _ _ = Poly.tt

open import CSP.Laws.FD.HideDivergence (Net-≟ {⊤})
  using (MAcc; macc; Hide-noDiv-from-MAcc)
open import CSP.Laws.Bisim.DRCongruence (Net-≟ {⊤})
  using (ModAStep; maτ; maE; DivModA)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {⊤})
  using (Par-τ-elim; ParτR; τL; τR
        ; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√
        ; Par-force-ret-inv)
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {⊤})
  using (Par-soloL; Par-soloR; Par-sync; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsHide (Net-≟ {⊤})
  using (Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√
        ; Hide-τ; Hide-keep; Hide-hidden
        ; fHide-ret-inv)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net-≟ {⊤})
  using (deadlock-no-τ; deadlock-no-ev)

NetR : Set
NetR = Poly.⊤ {0ℓ}

l0 : Link
l0 = fz

d0 : Dir
d0 = lo

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
inputAt = (⊤ , input fz lo N2N_KeepAlive)

inputLbl : Event√ NetR
inputLbl = evl (evLabel ⊤ (input fz lo N2N_KeepAlive) tt)

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
N1-no-output : vis-of (force N1) (⊤ , output fz lo N2N_KeepAlive) tt ≡ nothing
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
                  (pair (fin {n = 2}) (base (sndmsg fz lo N2N_KeepAlive))))

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
txIdx = _ , pair (fin {n = 2}) (base (tx fz lo N2N_KeepAlive))

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
                  (pair (fin {n = 2}) (base (rcvmsg fz lo N2N_KeepAlive))))

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
outputAt = (⊤ , output fz lo N2N_KeepAlive)

outputLbl : Event√ NetR
outputLbl = evl (evLabel ⊤ (output fz lo N2N_KeepAlive) tt)

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
                  (pair (fin {n = 2}) (base (sndack fz lo N2N_KeepAlive))))
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
ackIdx = _ , pair (fin {n = 2}) (base (ack fz lo N2N_KeepAlive))
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
                  (pair (fin {n = 2}) (base (rcvack fz lo N2N_KeepAlive))))
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

Input-stable : ∀ {t} → Input fz lo N2N_KeepAlive ─[ τ ]─► t → ⊥
Input-stable (sSil ())
Input-stable (sTau {i = _ , fin}                 refl ())
Input-stable (sTau {i = _ , base _}              refl ())
Input-stable (sTau {i = _ , pair fin (base _)}   refl ())
Input-stable (sTau {i = _ , pair fin fin}        refl ())
Input-stable (sTau {i = _ , pair fin (pair _ _)} refl ())
Input-stable (sTau {i = _ , pair (base _) _}     refl ())
Input-stable (sTau {i = _ , pair (pair _ _) _}   refl ())

Output-stable : ∀ {t} → Output fz lo N2N_KeepAlive ─[ τ ]─► t → ⊥
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
Inputs-no-sndmsg : ∀ {t a id} {l : Link} {d : Dir} →
  Inputs ─[ ev (evl (evLabel ⊤ (sndmsg l d id) a)) ]─► t → ⊥
Inputs-no-sndmsg (sVis refl ())

Inputs-no-rcvack : ∀ {t a id} {l : Link} {d : Dir} →
  Inputs ─[ ev (evl (evLabel ⊤ (rcvack l d id) a)) ]─► t → ⊥
Inputs-no-rcvack (sVis refl ())

-- Outputs refuses sndack on ANY id/connection (it offers only `rcvmsg`).
Outputs-no-sndack : ∀ {t a id} {l : Link} {d : Dir} →
  Outputs ─[ ev (evl (evLabel ⊤ (sndack l d id) a)) ]─► t → ⊥
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
  with Hide-τ-elim csSR' (Inputs ∥⇘ csSR' ⇙ (Transmitter ⦀ RcvAck)) step
... | hτP _ parτ _
      with Par-τ-elim csSR' ⊤merge Inputs (Transmitter ⦀ RcvAck) parτ
...   | τL _ Iτ  _ = Inputs-stable Iτ
...   | τR _ TRτ _ = TR-stable TRτ
TxSide-stable step
  | hτH {B} {e} {a} _ mem parev _
      with e
...   | sndmsg l d id with Par-ev-elim csSR' ⊤merge Inputs (Transmitter ⦀ RcvAck) parev
...     | evSync _ Iev _ = Inputs-no-sndmsg Iev
...     | evL  ¬cs _   = ¬cs mem
...     | evR  ¬cs _   = ¬cs mem
...     | evBoth ¬cs _ _ = ¬cs mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _
      | rcvack l d id with Par-ev-elim csSR' ⊤merge Inputs (Transmitter ⦀ RcvAck) parev
...     | evSync _ Iev _ = Inputs-no-rcvack Iev
...     | evL  ¬cs _   = ¬cs mem
...     | evR  ¬cs _   = ¬cs mem
...     | evBoth ¬cs _ _ = ¬cs mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | input l d id = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | output l d id = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | rcvmsg l d id = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | tx l d id = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | sndack l d id = mem
TxSide-stable step | hτH {B} {e} {a} _ mem parev _ | ack l d id = mem

-- Receiver offers only `tx`; SndAck offers only `sndack`.  Neither offers rcvmsg.
Receiver-no-rcvmsg : ∀ {t a id} {l : Link} {d : Dir} →
  Receiver ─[ ev (evl (evLabel ⊤ (rcvmsg l d id) a)) ]─► t → ⊥
Receiver-no-rcvmsg (sVis refl ())

SndAck-no-rcvmsg : ∀ {t a id} {l : Link} {d : Dir} →
  SndAck ─[ ev (evl (evLabel ⊤ (rcvmsg l d id) a)) ]─► t → ⊥
SndAck-no-rcvmsg (sVis refl ())

RS-no-rcvmsg : ∀ {t a id} {l : Link} {d : Dir} →
  (Receiver ⦀ SndAck) ─[ ev (evl (evLabel ⊤ (rcvmsg l d id) a)) ]─► t → ⊥
RS-no-rcvmsg step with Par-ev-elim ∅ES ⊤merge Receiver SndAck step
... | evSync mem _ _ = mem
... | evL  _ Rev   = Receiver-no-rcvmsg Rev
... | evR  _ Sev   = SndAck-no-rcvmsg Sev
... | evBoth _ Rev _ = Receiver-no-rcvmsg Rev

-- RxSide is τ-stable (symmetric to TxSide; hidden events rcvmsg/sndack).
RxSide-stable : ∀ {t} → RxSide ─[ τ ]─► t → ⊥
RxSide-stable step
  with Hide-τ-elim csRS' (Outputs ∥⇘ csRS' ⇙ (Receiver ⦀ SndAck)) step
... | hτP _ parτ _
      with Par-τ-elim csRS' ⊤merge Outputs (Receiver ⦀ SndAck) parτ
...   | τL _ Oτ  _ = Outputs-stable Oτ
...   | τR _ RSτ _ = RS-stable RSτ
RxSide-stable step
  | hτH {B} {e} {a} _ mem parev _
      with e
...   | rcvmsg l d id with Par-ev-elim csRS' ⊤merge Outputs (Receiver ⦀ SndAck) parev
...     | evSync _ _ RSev = RS-no-rcvmsg RSev
...     | evL  ¬cs _   = ¬cs mem
...     | evR  ¬cs _   = ¬cs mem
...     | evBoth ¬cs _ _ = ¬cs mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _
      | sndack l d id with Par-ev-elim csRS' ⊤merge Outputs (Receiver ⦀ SndAck) parev
...     | evSync _ Oev _ = Outputs-no-sndack Oev
...     | evL  ¬cs _   = ¬cs mem
...     | evR  ¬cs _   = ¬cs mem
...     | evBoth ¬cs _ _ = ¬cs mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | input l d id  = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | output l d id = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | sndmsg l d id = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | tx l d id     = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | rcvack l d id = mem
RxSide-stable step | hτH {B} {e} {a} _ mem parev _ | ack l d id    = mem

------------------------------------------------------------------------
-- SIDE NON-OFFER of the top sync events tx / ack.
--   TxSide offers input + ack (after hiding) but NOT tx.
--   RxSide offers output + tx (after hiding) but NOT ack.
------------------------------------------------------------------------

-- leaf/operand refusals of `tx`
Inputs-no-tx : ∀ {t a id} {l : Link} {d : Dir} →
  Inputs ─[ ev (evl (evLabel ⊤ (tx l d id) a)) ]─► t → ⊥
Inputs-no-tx (sVis refl ())

Transmitter-no-tx : ∀ {t a id} {l : Link} {d : Dir} →
  Transmitter ─[ ev (evl (evLabel ⊤ (tx l d id) a)) ]─► t → ⊥
Transmitter-no-tx (sVis refl ())

RcvAck-no-tx : ∀ {t a id} {l : Link} {d : Dir} →
  RcvAck ─[ ev (evl (evLabel ⊤ (tx l d id) a)) ]─► t → ⊥
RcvAck-no-tx (sVis refl ())

TR-no-tx : ∀ {t a id} {l : Link} {d : Dir} →
  (Transmitter ⦀ RcvAck) ─[ ev (evl (evLabel ⊤ (tx l d id) a)) ]─► t → ⊥
TR-no-tx step with Par-ev-elim ∅ES ⊤merge Transmitter RcvAck step
... | evSync mem _ _ = mem
... | evL  _ Tev   = Transmitter-no-tx Tev
... | evR  _ Rev   = RcvAck-no-tx Rev
... | evBoth _ Tev _ = Transmitter-no-tx Tev

-- TxSide does not offer `tx`.
TxSide-no-tx : ∀ {t a id} {l : Link} {d : Dir} →
  TxSide ─[ ev (evl (evLabel ⊤ (tx l d id) a)) ]─► t → ⊥
TxSide-no-tx step
  with Hide-ev-elim csSR' (Inputs ∥⇘ csSR' ⇙ (Transmitter ⦀ RcvAck)) step
... | heV _ _ parev with Par-ev-elim csSR' ⊤merge Inputs (Transmitter ⦀ RcvAck) parev
...   | evSync mem _ _ = mem
...   | evL  _ Iev   = Inputs-no-tx Iev
...   | evR  _ TRev  = TR-no-tx TRev
...   | evBoth _ Iev _ = Inputs-no-tx Iev

-- leaf/operand refusals of `ack`
Outputs-no-ack : ∀ {t a id} {l : Link} {d : Dir} →
  Outputs ─[ ev (evl (evLabel ⊤ (ack l d id) a)) ]─► t → ⊥
Outputs-no-ack (sVis refl ())

Receiver-no-ack : ∀ {t a id} {l : Link} {d : Dir} →
  Receiver ─[ ev (evl (evLabel ⊤ (ack l d id) a)) ]─► t → ⊥
Receiver-no-ack (sVis refl ())

SndAck-no-ack : ∀ {t a id} {l : Link} {d : Dir} →
  SndAck ─[ ev (evl (evLabel ⊤ (ack l d id) a)) ]─► t → ⊥
SndAck-no-ack (sVis refl ())

RS-no-ack : ∀ {t a id} {l : Link} {d : Dir} →
  (Receiver ⦀ SndAck) ─[ ev (evl (evLabel ⊤ (ack l d id) a)) ]─► t → ⊥
RS-no-ack step with Par-ev-elim ∅ES ⊤merge Receiver SndAck step
... | evSync mem _ _ = mem
... | evL  _ Rev   = Receiver-no-ack Rev
... | evR  _ Sev   = SndAck-no-ack Sev
... | evBoth _ Rev _ = Receiver-no-ack Rev

-- RxSide does not offer `ack`.
RxSide-no-ack : ∀ {t a id} {l : Link} {d : Dir} →
  RxSide ─[ ev (evl (evLabel ⊤ (ack l d id) a)) ]─► t → ⊥
RxSide-no-ack step
  with Hide-ev-elim csRS' (Outputs ∥⇘ csRS' ⇙ (Receiver ⦀ SndAck)) step
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
  ModAStep csTA' (TxSide ∥⇘ csTA' ⇙ RxSide) t → ⊥
Top-noModA (maτ parτ) with Par-τ-elim csTA' ⊤merge TxSide RxSide parτ
... | τL _ Tτ _ = TxSide-stable Tτ
... | τR _ Rτ _ = RxSide-stable Rτ
Top-noModA (maE {B} {e} {a} mem parev) with e
... | tx l d id with Par-ev-elim csTA' ⊤merge TxSide RxSide parev
...   | evSync _ Txev _ = TxSide-no-tx Txev
...   | evL  ¬cs _    = ¬cs mem
...   | evR  ¬cs _    = ¬cs mem
...   | evBoth ¬cs _ _ = ¬cs mem
Top-noModA (maE {B} {e} {a} mem parev) | ack l d id
      with Par-ev-elim csTA' ⊤merge TxSide RxSide parev
...   | evSync _ _ Rxev = RxSide-no-ack Rxev
...   | evL  ¬cs _    = ¬cs mem
...   | evR  ¬cs _    = ¬cs mem
...   | evBoth ¬cs _ _ = ¬cs mem
Top-noModA (maE {B} {e} {a} mem parev) | input l d id  = mem
Top-noModA (maE {B} {e} {a} mem parev) | output l d id = mem
Top-noModA (maE {B} {e} {a} mem parev) | sndmsg l d id = mem
Top-noModA (maE {B} {e} {a} mem parev) | rcvmsg l d id = mem
Top-noModA (maE {B} {e} {a} mem parev) | sndack l d id = mem
Top-noModA (maE {B} {e} {a} mem parev) | rcvack l d id = mem

Top-MAcc : MAcc csTA' (TxSide ∥⇘ csTA' ⇙ RxSide)
Top-MAcc = macc (λ step → ⊥-elim (Top-noModA step))

------------------------------------------------------------------------
-- MILESTONE 1 RESULT.  `Network = (Par⊤ csTA' TxSide RxSide) ∖ csTA'` is the
-- hide of a modulo-csTA accessible process, hence non-divergent.
------------------------------------------------------------------------

¬Diverges-Network : ¬ Diverges Network
¬Diverges-Network =
  Hide-noDiv-from-MAcc csTA' (TxSide ∥⇘ csTA' ⇙ RxSide) Top-MAcc

------------------------------------------------------------------------
-- Network is τ-stable at its initial (deadlocked) state: a τ of
-- `T ∖ csTA'` reflects to a modulo-csTA step of T, which `Top-noModA`
-- refutes.  (Reusable building block for the reachability analysis.)
------------------------------------------------------------------------

Network-noτ : ∀ {t} → Network ─[ τ ]─► t → ⊥
Network-noτ step with Hide-τ-elim csTA' (TxSide ∥⇘ csTA' ⇙ RxSide) step
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
T = TxSide ∥⇘ csTA' ⇙ RxSide

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
                  (pair (fin {n = 2}) (base (sndmsg fz lo N2N_KeepAlive)))
sndmsgValU : proj₁ sndmsgIdxU
sndmsgValU = lift fz , (lift (fs fz) , tt)

U2 : NetProc
U2 = succτ U1 sndmsgIdxU sndmsgValU

U1─τ─►U2 : U1 ─[ τ ]─► U2
U1─τ─►U2 = sTau {i = sndmsgIdxU} {a = sndmsgValU} refl refl

-- Second step: U2 fires `tx` as a VISIBLE sync between TxSide and RxSide.
-- At the un-hidden level this is `sVis`, NOT `sTau` (no outer hide).
txAt : AnyTypes (Net ⊤)
txAt = (⊤ , tx fz lo N2N_KeepAlive)

txLbl : Event√ NetR
txLbl = evl (evLabel ⊤ (tx fz lo N2N_KeepAlive) tt)

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
                  (pair (fin {n = 2}) (base (rcvmsg fz lo N2N_KeepAlive)))
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
                  (pair (fin {n = 2}) (base (sndack fz lo N2N_KeepAlive)))
sndackValU : proj₁ sndackIdxU
sndackValU = lift (fs fz) , (lift (fs fz) , tt)

U6 : NetProc
U6 = succτ U5 sndackIdxU sndackValU

U5─τ─►U6 : U5 ─[ τ ]─► U6
U5─τ─►U6 = sTau {i = sndackIdxU} {a = sndackValU} refl refl

-- U6 fires `ack` as a VISIBLE sync between RxSide and TxSide.
ackAt : AnyTypes (Net ⊤)
ackAt = (⊤ , ack fz lo N2N_KeepAlive)

ackLbl : Event√ NetR
ackLbl = evl (evLabel ⊤ (ack fz lo N2N_KeepAlive) tt)

-- Generalized labels (any d,id), annotated Event√ NetR so evl's R is pinned
-- (mirrors inputLbl/txLbl/ackLbl; used by the accept-any drainer disjuncts).
txLbl-at : Dir → IDs → Event√ NetR
txLbl-at d id = evl (evLabel ⊤ (tx fz d id) tt)
ackLbl-at : Dir → IDs → Event√ NetR
ackLbl-at d id = evl (evLabel ⊤ (ack fz d id) tt)

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
                  (pair (fin {n = 2}) (base (rcvack fz lo N2N_KeepAlive)))
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
sndmsgAtN = (⊤ , sndmsg fz lo N2N_KeepAlive)
rcvackAtN = (⊤ , rcvack fz lo N2N_KeepAlive)
ackAtN    = (⊤ , ack fz lo N2N_KeepAlive)
rcvmsgAtN = (⊤ , rcvmsg fz lo N2N_KeepAlive)
sndackAtN = (⊤ , sndack fz lo N2N_KeepAlive)

-- `output` is now ambiguous (re-exported twice); reuse the existing `outputAt`.
outputAtN : AnyTypes (Net ⊤)
outputAtN = outputAt

-- Leaf-level guard τ index (a `loop0` body that returned `ret tt` forces to
-- `sil (iter …)`; at the bare-leaf / Skip-padded ⦀ operand level the
-- restart-guard sits directly under the ⦀ tag of that operand).  The decI/decO
-- operands are `⦀⋆`-wrapped so their guard nests one `pair fin` deeper than the
-- bare Transmitter/etc.; the indices below are pinned by the `dec-Ui` probes.

------------------------------------------------------------------------
-- decI : the Inputs operand  ( ⦀⋆ [ Input fz lo N2N_KeepAlive ] -form ).
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
-- decO : the Outputs operand  ( ⦀⋆ [ Output fz lo N2N_KeepAlive ] -form ).
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
decTx i t r = ((decI i) ∥⇘ csSR' ⇙ (decT t ⦀ decR r)) ∖ csSR'

decRx : OP → CP → SP → NetProc
decRx o c s = ((decO o) ∥⇘ csRS' ⇙ (decC c ⦀ decS s)) ∖ csRS'

⟦_⟧ : CS → NetProc
⟦ mkCS i t r o c s ⟧ = (decTx i t r) ∥⇘ csTA' ⇙ (decRx o c s)

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

output′ : (l : Link) (d : Dir) (id : IDs) → Net ⊤ ⊤
output′ = NetQ.output

------------------------------------------------------------------------
-- decT : Transmitter.  T0 --sndmsg--> T1 ; T1 --tx--> Tg ; Tg --τ(sil)--> T0.
------------------------------------------------------------------------

-- T0 offers exactly `sndmsg` (→ T1) and nothing else; no τ.
decT-T0-noτ : ∀ {W} → decT T0 ─[ τ ]─► W → ⊥
decT-T0-noτ = Transmitter-stable

decT-T0-sndmsg : ∀ {a W} →
  decT T0 ─[ ev (evN (sndmsg fz lo N2N_KeepAlive) a) ]─► W → W ≡ decT T1
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
  decT T1 ─[ ev (evN (tx fz lo N2N_KeepAlive) a) ]─► W → W ≡ decT Tg
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
  decR R0 ─[ ev (evN (ack fz lo N2N_KeepAlive) a) ]─► W → W ≡ decR R1
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
  decR R1 ─[ ev (evN (rcvack fz lo N2N_KeepAlive) a) ]─► W → W ≡ decR Rg
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
  decC Rc0 ─[ ev (evN (tx fz lo N2N_KeepAlive) a) ]─► W → W ≡ decC Rc1
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
  decC Rc1 ─[ ev (evN (rcvmsg fz lo N2N_KeepAlive) a) ]─► W → W ≡ decC Rcg
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
  decS Sa0 ─[ ev (evN (sndack fz lo N2N_KeepAlive) a) ]─► W → W ≡ decS Sa1
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
  decS Sa1 ─[ ev (evN (ack fz lo N2N_KeepAlive) a) ]─► W → W ≡ decS Sag
decS-Sa1-ack (sVis refl refl) = refl

decS-Sag-τ : ∀ {W} → decS Sag ─[ τ ]─► W → W ≡ decS Sa0
decS-Sag-τ (sSil refl) = refl
decS-Sag-τ (sTau () _)

decS-Sag-noev : ∀ {B e a W} →
  decS Sag ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decS-Sag-noev (sVis () _)

------------------------------------------------------------------------
-- decI : the Inputs operand ( ⦀⋆ [ Input fz lo N2N_KeepAlive ] -form ).
--   I0 --input--> I1 ; I1 --sndmsg--> I2 ; I2 --rcvack--> Ig ; Ig --τ--> I0.
-- The ⦀⋆/⦀ Skip-padding collapses, so the active leaf's react surfaces at
-- the top; visible offers fire by `sVis refl refl`, and the restart guard
-- is the leaf `sil` (sSil refl).
------------------------------------------------------------------------

decI-I0-noτ : ∀ {W} → decI I0 ─[ τ ]─► W → ⊥
decI-I0-noτ = Inputs-stable

decI-I0-input : ∀ {a W} →
  decI I0 ─[ ev (evN (input fz lo N2N_KeepAlive) a) ]─► W → W ≡ decI I1
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
  decI I1 ─[ ev (evN (sndmsg fz lo N2N_KeepAlive) a) ]─► W → W ≡ decI I2
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
  decI I2 ─[ ev (evN (rcvack fz lo N2N_KeepAlive) a) ]─► W → W ≡ decI Ig
decI-I2-rcvack (sVis refl refl) = refl

decI-Ig-τ : ∀ {W} → decI Ig ─[ τ ]─► W → W ≡ decI I0
decI-Ig-τ (sSil refl) = refl
decI-Ig-τ (sTau () _)

decI-Ig-noev : ∀ {B e a W} →
  decI Ig ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decI-Ig-noev (sVis () _)

------------------------------------------------------------------------
-- decO : the Outputs operand ( ⦀⋆ [ Output fz lo N2N_KeepAlive ] -form ).
--   O0 --rcvmsg--> O1 ; O1 --output--> O2 ; O2 --sndack--> Og ; Og --τ--> O0.
------------------------------------------------------------------------

decO-O0-noτ : ∀ {W} → decO O0 ─[ τ ]─► W → ⊥
decO-O0-noτ = Outputs-stable

decO-O0-rcvmsg : ∀ {a W} →
  decO O0 ─[ ev (evN (rcvmsg fz lo N2N_KeepAlive) a) ]─► W → W ≡ decO O1
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
  decO O1 ─[ ev (evN (output′ fz lo N2N_KeepAlive) a) ]─► W → W ≡ decO O2
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
  decO O2 ─[ ev (evN (sndack fz lo N2N_KeepAlive) a) ]─► W → W ≡ decO Og
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
  decI i ─[ ev (evN (sndmsg fz lo N2N_KeepAlive) a) ]─► W → (i ≡ I1) × (W ≡ decI I2)
decI-sndmsg-class {I0} (sVis refl ())
decI-sndmsg-class {I1} step = refl , decI-I1-sndmsg step
decI-sndmsg-class {I2} (sVis refl ())
decI-sndmsg-class {Ig} step = ⊥-elim (decI-Ig-noev step)

-- decI offers `rcvack` only at I2 (→ Ig); refuse it at I0/I1/Ig.
decI-rcvack-class : ∀ {i a W} →
  decI i ─[ ev (evN (rcvack fz lo N2N_KeepAlive) a) ]─► W → (i ≡ I2) × (W ≡ decI Ig)
decI-rcvack-class {I0} (sVis refl ())
decI-rcvack-class {I1} (sVis refl ())
decI-rcvack-class {I2} step = refl , decI-I2-rcvack step
decI-rcvack-class {Ig} step = ⊥-elim (decI-Ig-noev step)

-- decT offers `sndmsg` only at T0 (→ T1); refuse it at T1/Tg.
decT-sndmsg-class : ∀ {t a W} →
  decT t ─[ ev (evN (sndmsg fz lo N2N_KeepAlive) a) ]─► W → (t ≡ T0) × (W ≡ decT T1)
decT-sndmsg-class {T0} step = refl , decT-T0-sndmsg step
decT-sndmsg-class {T1} (sVis refl ())
decT-sndmsg-class {Tg} step = ⊥-elim (decT-Tg-noev step)

-- decT refuses `rcvack` everywhere (it offers only sndmsg / tx).
decT-no-rcvack : ∀ {t a W d id} →
  decT t ─[ ev (evN (rcvack fz d id) a) ]─► W → ⊥
decT-no-rcvack {T0} (sVis refl ())
decT-no-rcvack {T1} (sVis refl ())
decT-no-rcvack {Tg} step = decT-Tg-noev step

-- decR offers `rcvack` only at R1 (→ Rg); refuse it at R0/Rg.
decR-rcvack-class : ∀ {r a W} →
  decR r ─[ ev (evN (rcvack fz lo N2N_KeepAlive) a) ]─► W → (r ≡ R1) × (W ≡ decR Rg)
decR-rcvack-class {R0} (sVis refl ())
decR-rcvack-class {R1} step = refl , decR-R1-rcvack step
decR-rcvack-class {Rg} step = ⊥-elim (decR-Rg-noev step)

-- decR refuses `sndmsg` everywhere (it offers only ack / rcvack).
decR-no-sndmsg : ∀ {r a W d id} →
  decR r ─[ ev (evN (sndmsg fz d id) a) ]─► W → ⊥
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
  (decT t ⦀ decR r) ─[ ev (evN (sndmsg fz lo N2N_KeepAlive) a) ]─► W →
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
  (decT t ⦀ decR r) ─[ ev (evN (rcvack fz lo N2N_KeepAlive) a) ]─► W →
  (r ≡ R1) × (W ≡ (decT t ⦀ decR Rg))
TR-rcvack-class {t} {r} step
  with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = ⊥-elim (decT-no-rcvack {t} Tev)
TR-rcvack-class {t} {r} step | evR  _ Rev = proj₁ cl , cong (λ z → decT t ⦀ z) (proj₂ cl)
  where cl = decR-rcvack-class {r} Rev
TR-rcvack-class {t} {r} step | evBoth _ Tev _ = ⊥-elim (decT-no-rcvack {t} Tev)

------------------------------------------------------------------------
-- Off-instance pinning: decI offers sndmsg/rcvack ONLY at the single
-- configured instance (fz , lo , N2N_KeepAlive); any step at (d,id) pins them.
-- (Config-driven medium: no cell exists for an unconfigured (d,id).)
------------------------------------------------------------------------
decI-sndmsg-pins : ∀ {i a W d id} →
  decI i ─[ ev (evN (sndmsg fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
decI-sndmsg-pins {I0} (sVis refl ())
decI-sndmsg-pins {I1} {a} {W} {d} {id} (sVis refl br)
  with Net-≟ {⊤} (⊤ , sndmsg fz lo N2N_KeepAlive) (⊤ , sndmsg fz d id) | br
... | yes refl | _  = refl , refl
... | no  _    | ()
decI-sndmsg-pins {I2} (sVis refl ())
decI-sndmsg-pins {Ig} step = ⊥-elim (decI-Ig-noev step)

decI-rcvack-pins : ∀ {i a W d id} →
  decI i ─[ ev (evN (rcvack fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
decI-rcvack-pins {I0} (sVis refl ())
decI-rcvack-pins {I1} (sVis refl ())
decI-rcvack-pins {I2} {a} {W} {d} {id} (sVis refl br)
  with Net-≟ {⊤} (⊤ , rcvack fz lo N2N_KeepAlive) (⊤ , rcvack fz d id) | br
... | yes refl | _  = refl , refl
... | no  _    | ()
decI-rcvack-pins {Ig} step = ⊥-elim (decI-Ig-noev step)

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
  with Hide-τ-elim csSR' ((decI i) ∥⇘ csSR' ⇙ (decT t ⦀ decR r)) step
-- (A) the inner Par's own τ: decI guard, or a τ of TR (decT/decR guard).
... | hτP _ parτ refl
      with Par-τ-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parτ
...   | τL _ Iτ refl =
        inj₂ (inj₂ (inj₁ (proj₁ cl ,
          cong (λ z → ((z ∥⇘ csSR' ⇙ (decT t ⦀ decR r)) ∖ csSR')) (proj₂ cl))))
  where cl = decI-τ-class Iτ
sim-Tx-τ {i} {t} {r} step | hτP _ parτ refl
      | τR _ TRτ refl with TR-τ-class TRτ
...     | inj₁ (gt , weq) =
          inj₂ (inj₂ (inj₂ (inj₁ (gt ,
            cong (λ z → (((decI i) ∥⇘ csSR' ⇙ z) ∖ csSR')) weq))))
...     | inj₂ (gr , weq) =
          inj₂ (inj₂ (inj₂ (inj₂ (gr ,
            cong (λ z → (((decI i) ∥⇘ csSR' ⇙ z) ∖ csSR')) weq))))
-- (B) a HIDDEN csSR-event of the inner Par: a sndmsg or rcvack SYNC.
sim-Tx-τ {i} {t} {r} step
  | hτH {B} {e} {a} _ mem parev refl with e
-- sndmsg sync: only N2N_KeepAlive has a connection (Conn id = Fin 0 elsewhere),
-- and Conn N2N_KeepAlive = Fin 1 = {zero=c0}; pin id/c, then classify.
... | sndmsg fz d id with d ≟ lo | id ≟ N2N_KeepAlive
...   | yes refl | yes refl with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...     | evSync _ Iev TRev = inj₁ (proj₁ clI , proj₁ clTR ,
            cong₂ (λ z w → ((z ∥⇘ csSR' ⇙ w) ∖ csSR')) (proj₂ clI) (proj₂ clTR))
  where clI  = decI-sndmsg-class {i} Iev
        clTR = TR-sndmsg-class {t} {r} TRev
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg fz d id | yes refl | yes refl
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg fz d id | yes refl | yes refl
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg fz d id | yes refl | yes refl
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg fz d id | no ¬d | _
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync _ Iev _  = ⊥-elim (¬d (proj₁ (decI-sndmsg-pins {i} Iev)))
...   | evL  ¬cs _      = ⊥-elim (¬cs mem)
...   | evR  ¬cs _      = ⊥-elim (¬cs mem)
...   | evBoth ¬cs _ _  = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg fz d id | yes refl | no ¬id
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync _ Iev _  = ⊥-elim (¬id (proj₂ (decI-sndmsg-pins {i} Iev)))
...   | evL  ¬cs _      = ⊥-elim (¬cs mem)
...   | evR  ¬cs _      = ⊥-elim (¬cs mem)
...   | evBoth ¬cs _ _  = ⊥-elim (¬cs mem)
-- rcvack sync: same id/c pinning.
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack fz d id
      with d ≟ lo | id ≟ N2N_KeepAlive
...   | yes refl | yes refl with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...     | evSync _ Iev TRev = inj₂ (inj₁ (proj₁ clR , proj₁ clI ,
            cong₂ (λ z w → ((z ∥⇘ csSR' ⇙ w) ∖ csSR')) (proj₂ clI) (proj₂ clR)))
  where clI = decI-rcvack-class {i} Iev
        clR = TR-rcvack-class {t} {r} TRev
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack fz d id | yes refl | yes refl
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack fz d id | yes refl | yes refl
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack fz d id | yes refl | yes refl
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack fz d id | no ¬d | _
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync _ Iev _  = ⊥-elim (¬d (proj₁ (decI-rcvack-pins {i} Iev)))
...   | evL  ¬cs _      = ⊥-elim (¬cs mem)
...   | evR  ¬cs _      = ⊥-elim (¬cs mem)
...   | evBoth ¬cs _ _  = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack fz d id | yes refl | no ¬id
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync _ Iev _  = ⊥-elim (¬id (proj₂ (decI-rcvack-pins {i} Iev)))
...   | evL  ¬cs _      = ⊥-elim (¬cs mem)
...   | evR  ¬cs _      = ⊥-elim (¬cs mem)
...   | evBoth ¬cs _ _  = ⊥-elim (¬cs mem)
-- non-csSR constructors: `mem : csSR' .mem (B,e) a = ⊥`.
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | input l d id  = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | output l d id = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg l d id = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | tx l d id     = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndack l d id = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | ack l d id    = ⊥-elim mem

------------------------------------------------------------------------
-- Operand-level visible-offer classifiers / refutations for the NON-csSR
-- events (input on decI; tx / ack on the TR side).  Fixed at the channel
-- `N2N_KeepAlive c0`; id-pinning is done at the sim-Tx-ev call site.
------------------------------------------------------------------------

-- decI offers `input` only at I0 (→ I1).
decI-input-class : ∀ {i a W} →
  decI i ─[ ev (evN (input fz lo N2N_KeepAlive) a) ]─► W → (i ≡ I0) × (W ≡ decI I1)
decI-input-class {I0} step = refl , decI-I0-input step
decI-input-class {I1} (sVis refl ())
decI-input-class {I2} (sVis refl ())
decI-input-class {Ig} step = ⊥-elim (decI-Ig-noev step)

-- decI refuses tx / ack / output / rcvmsg / sndack at every position.
decI-no-tx : ∀ {i a W d id} →
  decI i ─[ ev (evN (tx fz d id) a) ]─► W → ⊥
decI-no-tx {I0} (sVis refl ())
decI-no-tx {I1} (sVis refl ())
decI-no-tx {I2} (sVis refl ())
decI-no-tx {Ig} step = decI-Ig-noev step

decI-no-ack : ∀ {i a W d id} →
  decI i ─[ ev (evN (ack fz d id) a) ]─► W → ⊥
decI-no-ack {I0} (sVis refl ())
decI-no-ack {I1} (sVis refl ())
decI-no-ack {I2} (sVis refl ())
decI-no-ack {Ig} step = decI-Ig-noev step

decI-no-output : ∀ {i a W d id} →
  decI i ─[ ev (evN (output′ fz d id) a) ]─► W → ⊥
decI-no-output {I0} (sVis refl ())
decI-no-output {I1} (sVis refl ())
decI-no-output {I2} (sVis refl ())
decI-no-output {Ig} step = decI-Ig-noev step

decI-no-rcvmsg : ∀ {i a W d id} →
  decI i ─[ ev (evN (rcvmsg fz d id) a) ]─► W → ⊥
decI-no-rcvmsg {I0} (sVis refl ())
decI-no-rcvmsg {I1} (sVis refl ())
decI-no-rcvmsg {I2} (sVis refl ())
decI-no-rcvmsg {Ig} step = decI-Ig-noev step

decI-no-sndack : ∀ {i a W d id} →
  decI i ─[ ev (evN (sndack fz d id) a) ]─► W → ⊥
decI-no-sndack {I0} (sVis refl ())
decI-no-sndack {I1} (sVis refl ())
decI-no-sndack {I2} (sVis refl ())
decI-no-sndack {Ig} step = decI-Ig-noev step

-- decT refuses input / ack / output / rcvmsg / sndack at every position.
decT-no-input : ∀ {t a W d id} →
  decT t ─[ ev (evN (input fz d id) a) ]─► W → ⊥
decT-no-input {T0} (sVis refl ())
decT-no-input {T1} (sVis refl ())
decT-no-input {Tg} step = decT-Tg-noev step

decT-no-ack : ∀ {t a W d id} →
  decT t ─[ ev (evN (ack fz d id) a) ]─► W → ⊥
decT-no-ack {T0} (sVis refl ())
decT-no-ack {T1} (sVis refl ())
decT-no-ack {Tg} step = decT-Tg-noev step

decT-no-output : ∀ {t a W d id} →
  decT t ─[ ev (evN (output′ fz d id) a) ]─► W → ⊥
decT-no-output {T0} (sVis refl ())
decT-no-output {T1} (sVis refl ())
decT-no-output {Tg} step = decT-Tg-noev step

decT-no-rcvmsg : ∀ {t a W d id} →
  decT t ─[ ev (evN (rcvmsg fz d id) a) ]─► W → ⊥
decT-no-rcvmsg {T0} (sVis refl ())
decT-no-rcvmsg {T1} (sVis refl ())
decT-no-rcvmsg {Tg} step = decT-Tg-noev step

decT-no-sndack : ∀ {t a W d id} →
  decT t ─[ ev (evN (sndack fz d id) a) ]─► W → ⊥
decT-no-sndack {T0} (sVis refl ())
decT-no-sndack {T1} (sVis refl ())
decT-no-sndack {Tg} step = decT-Tg-noev step

-- decT offers `tx` only at T1 (→ Tg).
decT-tx-class : ∀ {t a W} →
  decT t ─[ ev (evN (tx fz lo N2N_KeepAlive) a) ]─► W → (t ≡ T1) × (W ≡ decT Tg)
decT-tx-class {T0} (sVis refl ())
decT-tx-class {T1} step = refl , decT-T1-tx step
decT-tx-class {Tg} step = ⊥-elim (decT-Tg-noev step)

-- decR refuses input / tx / output / rcvmsg / sndack at every position.
decR-no-input : ∀ {r a W d id} →
  decR r ─[ ev (evN (input fz d id) a) ]─► W → ⊥
decR-no-input {R0} (sVis refl ())
decR-no-input {R1} (sVis refl ())
decR-no-input {Rg} step = decR-Rg-noev step

decR-no-tx : ∀ {r a W d id} →
  decR r ─[ ev (evN (tx fz d id) a) ]─► W → ⊥
decR-no-tx {R0} (sVis refl ())
decR-no-tx {R1} (sVis refl ())
decR-no-tx {Rg} step = decR-Rg-noev step

decR-no-output : ∀ {r a W d id} →
  decR r ─[ ev (evN (output′ fz d id) a) ]─► W → ⊥
decR-no-output {R0} (sVis refl ())
decR-no-output {R1} (sVis refl ())
decR-no-output {Rg} step = decR-Rg-noev step

decR-no-rcvmsg : ∀ {r a W d id} →
  decR r ─[ ev (evN (rcvmsg fz d id) a) ]─► W → ⊥
decR-no-rcvmsg {R0} (sVis refl ())
decR-no-rcvmsg {R1} (sVis refl ())
decR-no-rcvmsg {Rg} step = decR-Rg-noev step

decR-no-sndack : ∀ {r a W d id} →
  decR r ─[ ev (evN (sndack fz d id) a) ]─► W → ⊥
decR-no-sndack {R0} (sVis refl ())
decR-no-sndack {R1} (sVis refl ())
decR-no-sndack {Rg} step = decR-Rg-noev step

-- decR offers `ack` only at R0 (→ R1).
decR-ack-class : ∀ {r a W} →
  decR r ─[ ev (evN (ack fz lo N2N_KeepAlive) a) ]─► W → (r ≡ R0) × (W ≡ decR R1)
decR-ack-class {R0} step = refl , decR-R0-ack step
decR-ack-class {R1} (sVis refl ())
decR-ack-class {Rg} step = ⊥-elim (decR-Rg-noev step)

------------------------------------------------------------------------
-- TR-side visible-offer classifiers / refutations.
------------------------------------------------------------------------

-- TR offers `tx` only via decT at T1 (→ Tg); decR refuses tx ⇒ decT-solo.
TR-tx-class : ∀ {t r a W} →
  (decT t ⦀ decR r) ─[ ev (evN (tx fz lo N2N_KeepAlive) a) ]─► W →
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
  (decT t ⦀ decR r) ─[ ev (evN (ack fz lo N2N_KeepAlive) a) ]─► W →
  (r ≡ R0) × (W ≡ (decT t ⦀ decR R1))
TR-ack-class {t} {r} step
  with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = ⊥-elim (decT-no-ack {t} Tev)
TR-ack-class {t} {r} step | evR  _ Rev = proj₁ cl , cong (λ z → decT t ⦀ z) (proj₂ cl)
  where cl = decR-ack-class {r} Rev
TR-ack-class {t} {r} step | evBoth _ Tev _ = ⊥-elim (decT-no-ack {t} Tev)

-- TR refuses input / output / rcvmsg / sndack at every position.
TR-no-input : ∀ {t r a W d id} →
  (decT t ⦀ decR r) ─[ ev (evN (input fz d id) a) ]─► W → ⊥
TR-no-input {t} {r} step with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-input {t} Tev
... | evR  _ Rev       = decR-no-input {r} Rev
... | evBoth _ Tev _   = decT-no-input {t} Tev

TR-no-output : ∀ {t r a W d id} →
  (decT t ⦀ decR r) ─[ ev (evN (output′ fz d id) a) ]─► W → ⊥
TR-no-output {t} {r} step with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-output {t} Tev
... | evR  _ Rev       = decR-no-output {r} Rev
... | evBoth _ Tev _   = decT-no-output {t} Tev

TR-no-rcvmsg : ∀ {t r a W d id} →
  (decT t ⦀ decR r) ─[ ev (evN (rcvmsg fz d id) a) ]─► W → ⊥
TR-no-rcvmsg {t} {r} step with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-rcvmsg {t} Tev
... | evR  _ Rev       = decR-no-rcvmsg {r} Rev
... | evBoth _ Tev _   = decT-no-rcvmsg {t} Tev

TR-no-sndack : ∀ {t r a W d id} →
  (decT t ⦀ decR r) ─[ ev (evN (sndack fz d id) a) ]─► W → ⊥
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

------------------------------------------------------------------------
-- Off-instance pinning for the visible-offer channels (input/tx/ack).
------------------------------------------------------------------------
decI-input-pins : ∀ {i a W d id} →
  decI i ─[ ev (evN (input fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
decI-input-pins {I0} {d = lo} {id = N2N_KeepAlive}    _              = refl , refl
decI-input-pins {I0} {d = lo} {id = N2N_ChainSync}    (sVis refl ())
decI-input-pins {I0} {d = lo} {id = N2N_BlockFetch}   (sVis refl ())
decI-input-pins {I0} {d = lo} {id = N2N_TxSubmission} (sVis refl ())
decI-input-pins {I0} {d = lo} {id = N2N_LeiosNotify}  (sVis refl ())
decI-input-pins {I0} {d = lo} {id = N2N_LeiosFetch}   (sVis refl ())
decI-input-pins {I0} {d = hi} {id}                    (sVis refl ())
decI-input-pins {I1} (sVis refl ())
decI-input-pins {I2} (sVis refl ())
decI-input-pins {Ig} step = ⊥-elim (decI-Ig-noev step)

decT-tx-pins : ∀ {t a W d id} →
  decT t ─[ ev (evN (tx fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
decT-tx-pins {T0} (sVis refl ())
decT-tx-pins {T1} {a} {W} {d} {id} (sVis refl br)
  with Net-≟ {⊤} (⊤ , tx fz lo N2N_KeepAlive) (⊤ , tx fz d id) | br
... | yes refl | _  = refl , refl
... | no  _    | ()
decT-tx-pins {Tg} step = ⊥-elim (decT-Tg-noev step)

decR-ack-class-gen : ∀ {r a W d id} →
  decR r ─[ ev (evN (ack fz d id) a) ]─► W →
  (r ≡ R0) × (W ≡ succV RcvAck (⊤ , ack fz d id) a)
decR-ack-class-gen {R0} (sVis refl refl) = refl , refl
decR-ack-class-gen {R1} (sVis refl ())
decR-ack-class-gen {Rg} step = ⊥-elim (decR-Rg-noev step)

TR-tx-pins : ∀ {t r a W d id} →
  (decT t ⦀ decR r) ─[ ev (evN (tx fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
TR-tx-pins {t} {r} step with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _  = ⊥-elim mem
... | evL  _ Tev      = decT-tx-pins {t} Tev
... | evR  _ Rev      = ⊥-elim (decR-no-tx {r} Rev)
... | evBoth _ Tev _  = decT-tx-pins {t} Tev

TR-ack-class-gen : ∀ {t r a W d id} →
  (decT t ⦀ decR r) ─[ ev (evN (ack fz d id) a) ]─► W →
  (r ≡ R0) × (W ≡ (decT t ⦀ succV RcvAck (⊤ , ack fz d id) a))
TR-ack-class-gen {t} {r} step with Par-ev-elim ∅ES ⊤merge (decT t) (decR r) step
... | evSync mem _ _  = ⊥-elim mem
... | evL  _ Tev      = ⊥-elim (decT-no-ack {t} Tev)
... | evR  _ Rev      = proj₁ cl , cong (λ z → decT t ⦀ z) (proj₂ cl)
  where cl = decR-ack-class-gen {r} Rev
... | evBoth _ Tev _  = ⊥-elim (decT-no-ack {t} Tev)

sim-Tx-ev : ∀ {i t r B} {e : Net ⊤ B} {a} {W} →
  decTx i t r ─[ ev (evl (evLabel B e a)) ]─► W →
    ((i ≡ I0) × (evl (evLabel B e a) ≡ inputLbl) × (W ≡ decTx I1 t r))
  ⊎ ((t ≡ T1) × (evl (evLabel B e a) ≡ txLbl)    × (W ≡ decTx i Tg r))
  ⊎ ((r ≡ R0) × Σ[ d ∈ Dir ] Σ[ id ∈ IDs ]
        (evl (evLabel B e a) ≡ ackLbl-at d id)
      × (W ≡ ((decI i) ∥⇘ csSR' ⇙ (decT t ⦀ succV RcvAck (⊤ , ack fz d id) tt)) ∖ csSR'))
sim-Tx-ev {i} {t} {r} step
  with Hide-ev-elim csSR' ((decI i) ∥⇘ csSR' ⇙ (decT t ⦀ decR r)) step
... | heV {B} {e} {a} _ ¬cs parev with e
-- input (offered solo by decI at I0): pin (d,id) = (lo,KA).
... | input fz d id with d ≟ lo | id ≟ N2N_KeepAlive
...   | yes refl | yes refl with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...     | evSync mem _ _   = ⊥-elim mem
...     | evL  _ Iev       = inj₁ (proj₁ cl , refl ,
            cong (λ z → ((z ∥⇘ csSR' ⇙ (decT t ⦀ decR r)) ∖ csSR')) (proj₂ cl))
  where cl = decI-input-class {i} Iev
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | input fz d id | yes refl | yes refl
      | evR  _ TRev      = ⊥-elim (TR-no-input {t} {r} TRev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | input fz d id | yes refl | yes refl
      | evBoth _ _ TRev  = ⊥-elim (TR-no-input {t} {r} TRev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | input fz d id | no ¬d | _
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (¬d (proj₁ (decI-input-pins {i} Iev)))
...   | evR  _ TRev      = ⊥-elim (TR-no-input {t} {r} TRev)
...   | evBoth _ _ TRev  = ⊥-elim (TR-no-input {t} {r} TRev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | input fz d id | yes refl | no ¬id
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (¬id (proj₂ (decI-input-pins {i} Iev)))
...   | evR  _ TRev      = ⊥-elim (TR-no-input {t} {r} TRev)
...   | evBoth _ _ TRev  = ⊥-elim (TR-no-input {t} {r} TRev)
-- tx (offered solo by TR at T1): pin.
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx fz d id with d ≟ lo | id ≟ N2N_KeepAlive
...   | yes refl | yes refl with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...     | evSync mem _ _   = ⊥-elim mem
...     | evL  _ Iev       = ⊥-elim (decI-no-tx {i} Iev)
...     | evR  _ TRev      = inj₂ (inj₁ (proj₁ cl , refl ,
            cong (λ z → (((decI i) ∥⇘ csSR' ⇙ z) ∖ csSR')) (proj₂ cl)))
  where cl = TR-tx-class {t} {r} TRev
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx fz d id | yes refl | yes refl
      | evBoth _ Iev _   = ⊥-elim (decI-no-tx {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx fz d id | no ¬d | _
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-tx {i} Iev)
...   | evR  _ TRev      = ⊥-elim (¬d (proj₁ (TR-tx-pins {t} {r} TRev)))
...   | evBoth _ Iev _   = ⊥-elim (decI-no-tx {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx fz d id | yes refl | no ¬id
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-tx {i} Iev)
...   | evR  _ TRev      = ⊥-elim (¬id (proj₂ (TR-tx-pins {t} {r} TRev)))
...   | evBoth _ Iev _   = ⊥-elim (decI-no-tx {i} Iev)
-- ack (offered solo by TR at R0): pin.
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack fz d id
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-ack {i} Iev)
...   | evR  _ TRev      = inj₂ (inj₂ (proj₁ cl , d , id , refl ,
            cong (λ z → (((decI i) ∥⇘ csSR' ⇙ z) ∖ csSR')) (proj₂ cl)))
  where cl = TR-ack-class-gen {t} {r} TRev
...   | evBoth _ Iev _   = ⊥-elim (decI-no-ack {i} Iev)
-- sndmsg / rcvack: ∈csSR', so ¬cs is ¬⊤ ⇒ absurd.
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndmsg l d id = ⊥-elim (¬cs Poly.tt)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvack l d id = ⊥-elim (¬cs Poly.tt)
-- output / rcvmsg / sndack: neither operand offers them (any d,id) ⇒ refute.
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output fz d id
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-output {i} Iev)
...   | evR  _ TRev      = ⊥-elim (TR-no-output {t} {r} TRev)
...   | evBoth _ Iev _   = ⊥-elim (decI-no-output {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg fz d id
      with Par-ev-elim csSR' ⊤merge (decI i) (decT t ⦀ decR r) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-rcvmsg {i} Iev)
...   | evR  _ TRev      = ⊥-elim (TR-no-rcvmsg {t} {r} TRev)
...   | evBoth _ Iev _   = ⊥-elim (decI-no-rcvmsg {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack fz d id
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
  decO o ─[ ev (evN (rcvmsg fz lo N2N_KeepAlive) a) ]─► W → (o ≡ O0) × (W ≡ decO O1)
decO-rcvmsg-class {O0} step = refl , decO-O0-rcvmsg step
decO-rcvmsg-class {O1} (sVis refl ())
decO-rcvmsg-class {O2} (sVis refl ())
decO-rcvmsg-class {Og} step = ⊥-elim (decO-Og-noev step)

-- decO offers `sndack` only at O2 (→ Og); refuse it at O0/O1/Og.
decO-sndack-class : ∀ {o a W} →
  decO o ─[ ev (evN (sndack fz lo N2N_KeepAlive) a) ]─► W → (o ≡ O2) × (W ≡ decO Og)
decO-sndack-class {O0} (sVis refl ())
decO-sndack-class {O1} (sVis refl ())
decO-sndack-class {O2} step = refl , decO-O2-sndack step
decO-sndack-class {Og} step = ⊥-elim (decO-Og-noev step)

-- decO-rcvmsg-pins : rcvmsg is accepted (menu) by Outputs only at (lo, KA).
decO-rcvmsg-pins : ∀ {o a W d id} →
  decO o ─[ ev (evN (rcvmsg fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
decO-rcvmsg-pins {O0} {d = lo} {id = N2N_KeepAlive}    _              = refl , refl
decO-rcvmsg-pins {O0} {d = lo} {id = N2N_ChainSync}    (sVis refl ())
decO-rcvmsg-pins {O0} {d = lo} {id = N2N_BlockFetch}   (sVis refl ())
decO-rcvmsg-pins {O0} {d = lo} {id = N2N_TxSubmission} (sVis refl ())
decO-rcvmsg-pins {O0} {d = lo} {id = N2N_LeiosNotify}  (sVis refl ())
decO-rcvmsg-pins {O0} {d = lo} {id = N2N_LeiosFetch}   (sVis refl ())
decO-rcvmsg-pins {O0} {d = hi} {id}                    (sVis refl ())
decO-rcvmsg-pins {O1} (sVis refl ())
decO-rcvmsg-pins {O2} (sVis refl ())
decO-rcvmsg-pins {Og} step = ⊥-elim (decO-Og-noev step)

-- decO-sndack-pins : sndack is emitted (Prefix) by Outputs only at (lo, KA).
decO-sndack-pins : ∀ {o a W d id} →
  decO o ─[ ev (evN (sndack fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
decO-sndack-pins {O0} (sVis refl ())
decO-sndack-pins {O1} (sVis refl ())
decO-sndack-pins {O2} {a} {W} {d} {id} (sVis refl br)
  with Net-≟ {⊤} (⊤ , sndack fz lo N2N_KeepAlive) (⊤ , sndack fz d id) | br
... | yes refl | _  = refl , refl
... | no  _    | ()
decO-sndack-pins {Og} step = ⊥-elim (decO-Og-noev step)

-- decC (Receiver) offers `rcvmsg` only at Rc1 (→ Rcg); refuse it at Rc0/Rcg.
decC-rcvmsg-class : ∀ {c a W} →
  decC c ─[ ev (evN (rcvmsg fz lo N2N_KeepAlive) a) ]─► W → (c ≡ Rc1) × (W ≡ decC Rcg)
decC-rcvmsg-class {Rc0} (sVis refl ())
decC-rcvmsg-class {Rc1} step = refl , decC-Rc1-rcvmsg step
decC-rcvmsg-class {Rcg} step = ⊥-elim (decC-Rcg-noev step)

-- decC refuses `sndack` everywhere (it offers only tx / rcvmsg).
decC-no-sndack : ∀ {c a W d id} →
  decC c ─[ ev (evN (sndack fz d id) a) ]─► W → ⊥
decC-no-sndack {Rc0} (sVis refl ())
decC-no-sndack {Rc1} (sVis refl ())
decC-no-sndack {Rcg} step = decC-Rcg-noev step

-- decS (SndAck) offers `sndack` only at Sa0 (→ Sa1); refuse it at Sa1/Sag.
decS-sndack-class : ∀ {s a W} →
  decS s ─[ ev (evN (sndack fz lo N2N_KeepAlive) a) ]─► W → (s ≡ Sa0) × (W ≡ decS Sa1)
decS-sndack-class {Sa0} step = refl , decS-Sa0-sndack step
decS-sndack-class {Sa1} (sVis refl ())
decS-sndack-class {Sag} step = ⊥-elim (decS-Sag-noev step)

-- decS refuses `rcvmsg` everywhere (it offers only sndack / ack).
decS-no-rcvmsg : ∀ {s a W d id} →
  decS s ─[ ev (evN (rcvmsg fz d id) a) ]─► W → ⊥
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
  (decC c ⦀ decS s) ─[ ev (evN (rcvmsg fz lo N2N_KeepAlive) a) ]─► W →
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
  (decC c ⦀ decS s) ─[ ev (evN (sndack fz lo N2N_KeepAlive) a) ]─► W →
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
  with Hide-τ-elim csRS' ((decO o) ∥⇘ csRS' ⇙ (decC c ⦀ decS s)) step
-- (A) the inner Par's own τ: decO guard, or a τ of RS (decC/decS guard).
... | hτP _ parτ refl
      with Par-τ-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parτ
...   | τL _ Oτ refl =
        inj₂ (inj₂ (inj₁ (proj₁ cl ,
          cong (λ z → ((z ∥⇘ csRS' ⇙ (decC c ⦀ decS s)) ∖ csRS')) (proj₂ cl))))
  where cl = decO-τ-class Oτ
sim-Rx-τ {o} {c} {s} step | hτP _ parτ refl
      | τR _ RSτ refl with RS-τ-class RSτ
...     | inj₁ (gc , weq) =
          inj₂ (inj₂ (inj₂ (inj₁ (gc ,
            cong (λ z → (((decO o) ∥⇘ csRS' ⇙ z) ∖ csRS')) weq))))
...     | inj₂ (gs , weq) =
          inj₂ (inj₂ (inj₂ (inj₂ (gs ,
            cong (λ z → (((decO o) ∥⇘ csRS' ⇙ z) ∖ csRS')) weq))))
-- (B) a HIDDEN csRS-event of the inner Par: a rcvmsg or sndack SYNC.
sim-Rx-τ {o} {c} {s} step
  | hτH {B} {e} {a} _ mem parev refl with e
-- rcvmsg sync: pin (d,id)=(lo,KA) (Outputs accepts only there), then classify.
... | rcvmsg fz d id with d ≟ lo | id ≟ N2N_KeepAlive
...   | yes refl | yes refl with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...     | evSync _ Oev RSev = inj₁ (proj₁ clRS , proj₁ clO ,
            cong₂ (λ z w → ((z ∥⇘ csRS' ⇙ w) ∖ csRS')) (proj₂ clO) (proj₂ clRS))
  where clO  = decO-rcvmsg-class {o} Oev
        clRS = RS-rcvmsg-class {c} {s} RSev
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg fz d id | yes refl | yes refl
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg fz d id | yes refl | yes refl
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg fz d id | yes refl | yes refl
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg fz d id | no ¬d | _
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync _ Oev _  = ⊥-elim (¬d (proj₁ (decO-rcvmsg-pins {o} Oev)))
...   | evL  ¬cs _      = ⊥-elim (¬cs mem)
...   | evR  ¬cs _      = ⊥-elim (¬cs mem)
...   | evBoth ¬cs _ _  = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg fz d id | yes refl | no ¬id
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync _ Oev _  = ⊥-elim (¬id (proj₂ (decO-rcvmsg-pins {o} Oev)))
...   | evL  ¬cs _      = ⊥-elim (¬cs mem)
...   | evR  ¬cs _      = ⊥-elim (¬cs mem)
...   | evBoth ¬cs _ _  = ⊥-elim (¬cs mem)
-- sndack sync: same id/c pinning.
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack fz d id
      with d ≟ lo | id ≟ N2N_KeepAlive
...   | yes refl | yes refl with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...     | evSync _ Oev RSev = inj₂ (inj₁ (proj₁ clO , proj₁ clRS ,
            cong₂ (λ z w → ((z ∥⇘ csRS' ⇙ w) ∖ csRS')) (proj₂ clO) (proj₂ clRS)))
  where clO  = decO-sndack-class {o} Oev
        clRS = RS-sndack-class {c} {s} RSev
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack fz d id | yes refl | yes refl
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack fz d id | yes refl | yes refl
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack fz d id | yes refl | yes refl
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack fz d id | no ¬d | _
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync _ Oev _  = ⊥-elim (¬d (proj₁ (decO-sndack-pins {o} Oev)))
...   | evL  ¬cs _      = ⊥-elim (¬cs mem)
...   | evR  ¬cs _      = ⊥-elim (¬cs mem)
...   | evBoth ¬cs _ _  = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack fz d id | yes refl | no ¬id
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync _ Oev _  = ⊥-elim (¬id (proj₂ (decO-sndack-pins {o} Oev)))
...   | evL  ¬cs _      = ⊥-elim (¬cs mem)
...   | evR  ¬cs _      = ⊥-elim (¬cs mem)
...   | evBoth ¬cs _ _  = ⊥-elim (¬cs mem)
-- non-csRS constructors: `mem : csRS' .mem (B,e) a = ⊥`.
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | input l d id′  = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | output l d id′ = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | tx l d id′     = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndmsg l d id′ = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvack l d id′ = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | ack l d id′    = ⊥-elim mem

------------------------------------------------------------------------
-- Operand-level visible-offer classifiers / refutations for the NON-csRS
-- events (output on decO; tx / ack on the RS side).  Fixed at the channel
-- `N2N_KeepAlive c0`; id-pinning is done at the sim-Rx-ev call site.
------------------------------------------------------------------------

-- decO offers `output` only at O1 (→ O2).
decO-output-class : ∀ {o a W} →
  decO o ─[ ev (evN (output′ fz lo N2N_KeepAlive) a) ]─► W → (o ≡ O1) × (W ≡ decO O2)
decO-output-class {O0} (sVis refl ())
decO-output-class {O1} step = refl , decO-O1-output step
decO-output-class {O2} (sVis refl ())
decO-output-class {Og} step = ⊥-elim (decO-Og-noev step)

-- decO refuses tx / ack / input / sndmsg / rcvack at every position.
decO-no-tx : ∀ {o a W d id} →
  decO o ─[ ev (evN (tx fz d id) a) ]─► W → ⊥
decO-no-tx {O0} (sVis refl ())
decO-no-tx {O1} (sVis refl ())
decO-no-tx {O2} (sVis refl ())
decO-no-tx {Og} step = decO-Og-noev step

decO-no-ack : ∀ {o a W d id} →
  decO o ─[ ev (evN (ack fz d id) a) ]─► W → ⊥
decO-no-ack {O0} (sVis refl ())
decO-no-ack {O1} (sVis refl ())
decO-no-ack {O2} (sVis refl ())
decO-no-ack {Og} step = decO-Og-noev step

decO-no-input : ∀ {o a W d id} →
  decO o ─[ ev (evN (input fz d id) a) ]─► W → ⊥
decO-no-input {O0} (sVis refl ())
decO-no-input {O1} (sVis refl ())
decO-no-input {O2} (sVis refl ())
decO-no-input {Og} step = decO-Og-noev step

decO-no-sndmsg : ∀ {o a W d id} →
  decO o ─[ ev (evN (sndmsg fz d id) a) ]─► W → ⊥
decO-no-sndmsg {O0} (sVis refl ())
decO-no-sndmsg {O1} (sVis refl ())
decO-no-sndmsg {O2} (sVis refl ())
decO-no-sndmsg {Og} step = decO-Og-noev step

decO-no-rcvack : ∀ {o a W d id} →
  decO o ─[ ev (evN (rcvack fz d id) a) ]─► W → ⊥
decO-no-rcvack {O0} (sVis refl ())
decO-no-rcvack {O1} (sVis refl ())
decO-no-rcvack {O2} (sVis refl ())
decO-no-rcvack {Og} step = decO-Og-noev step

-- decC (Receiver) offers `tx` only at Rc0 (→ Rc1).
decC-tx-class : ∀ {c a W} →
  decC c ─[ ev (evN (tx fz lo N2N_KeepAlive) a) ]─► W → (c ≡ Rc0) × (W ≡ decC Rc1)
decC-tx-class {Rc0} step = refl , decC-Rc0-tx step
decC-tx-class {Rc1} (sVis refl ())
decC-tx-class {Rcg} step = ⊥-elim (decC-Rcg-noev step)

-- decC refuses output / ack / input / sndmsg / rcvack at every position.
decC-no-output : ∀ {c a W d id} →
  decC c ─[ ev (evN (output′ fz d id) a) ]─► W → ⊥
decC-no-output {Rc0} (sVis refl ())
decC-no-output {Rc1} (sVis refl ())
decC-no-output {Rcg} step = decC-Rcg-noev step

decC-no-ack : ∀ {c a W d id} →
  decC c ─[ ev (evN (ack fz d id) a) ]─► W → ⊥
decC-no-ack {Rc0} (sVis refl ())
decC-no-ack {Rc1} (sVis refl ())
decC-no-ack {Rcg} step = decC-Rcg-noev step

decC-no-input : ∀ {c a W d id} →
  decC c ─[ ev (evN (input fz d id) a) ]─► W → ⊥
decC-no-input {Rc0} (sVis refl ())
decC-no-input {Rc1} (sVis refl ())
decC-no-input {Rcg} step = decC-Rcg-noev step

decC-no-sndmsg : ∀ {c a W d id} →
  decC c ─[ ev (evN (sndmsg fz d id) a) ]─► W → ⊥
decC-no-sndmsg {Rc0} (sVis refl ())
decC-no-sndmsg {Rc1} (sVis refl ())
decC-no-sndmsg {Rcg} step = decC-Rcg-noev step

decC-no-rcvack : ∀ {c a W d id} →
  decC c ─[ ev (evN (rcvack fz d id) a) ]─► W → ⊥
decC-no-rcvack {Rc0} (sVis refl ())
decC-no-rcvack {Rc1} (sVis refl ())
decC-no-rcvack {Rcg} step = decC-Rcg-noev step

-- decS (SndAck) offers `ack` only at Sa1 (→ Sag).
decS-ack-class : ∀ {s a W} →
  decS s ─[ ev (evN (ack fz lo N2N_KeepAlive) a) ]─► W → (s ≡ Sa1) × (W ≡ decS Sag)
decS-ack-class {Sa0} (sVis refl ())
decS-ack-class {Sa1} step = refl , decS-Sa1-ack step
decS-ack-class {Sag} step = ⊥-elim (decS-Sag-noev step)

-- decS refuses output / tx / input / sndmsg / rcvack at every position.
decS-no-output : ∀ {s a W d id} →
  decS s ─[ ev (evN (output′ fz d id) a) ]─► W → ⊥
decS-no-output {Sa0} (sVis refl ())
decS-no-output {Sa1} (sVis refl ())
decS-no-output {Sag} step = decS-Sag-noev step

decS-no-tx : ∀ {s a W d id} →
  decS s ─[ ev (evN (tx fz d id) a) ]─► W → ⊥
decS-no-tx {Sa0} (sVis refl ())
decS-no-tx {Sa1} (sVis refl ())
decS-no-tx {Sag} step = decS-Sag-noev step

decS-no-input : ∀ {s a W d id} →
  decS s ─[ ev (evN (input fz d id) a) ]─► W → ⊥
decS-no-input {Sa0} (sVis refl ())
decS-no-input {Sa1} (sVis refl ())
decS-no-input {Sag} step = decS-Sag-noev step

decS-no-sndmsg : ∀ {s a W d id} →
  decS s ─[ ev (evN (sndmsg fz d id) a) ]─► W → ⊥
decS-no-sndmsg {Sa0} (sVis refl ())
decS-no-sndmsg {Sa1} (sVis refl ())
decS-no-sndmsg {Sag} step = decS-Sag-noev step

decS-no-rcvack : ∀ {s a W d id} →
  decS s ─[ ev (evN (rcvack fz d id) a) ]─► W → ⊥
decS-no-rcvack {Sa0} (sVis refl ())
decS-no-rcvack {Sa1} (sVis refl ())
decS-no-rcvack {Sag} step = decS-Sag-noev step

------------------------------------------------------------------------
-- RS-side visible-offer classifiers / refutations.
------------------------------------------------------------------------

-- RS offers `tx` only via decC at Rc0 (→ Rc1); decS refuses tx ⇒ decC-solo.
RS-tx-class : ∀ {c s a W} →
  (decC c ⦀ decS s) ─[ ev (evN (tx fz lo N2N_KeepAlive) a) ]─► W →
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
  (decC c ⦀ decS s) ─[ ev (evN (ack fz lo N2N_KeepAlive) a) ]─► W →
  (s ≡ Sa1) × (W ≡ (decC c ⦀ decS Sag))
RS-ack-class {c} {s} step
  with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = ⊥-elim (decC-no-ack {c} Cev)
RS-ack-class {c} {s} step | evR  _ Sev = proj₁ cl , cong (λ z → decC c ⦀ z) (proj₂ cl)
  where cl = decS-ack-class {s} Sev
RS-ack-class {c} {s} step | evBoth _ Cev _ = ⊥-elim (decC-no-ack {c} Cev)

-- RS refuses output / input / sndmsg / rcvack at every position.
RS-no-output : ∀ {c s a W d id} →
  (decC c ⦀ decS s) ─[ ev (evN (output′ fz d id) a) ]─► W → ⊥
RS-no-output {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-output {c} Cev
... | evR  _ Sev       = decS-no-output {s} Sev
... | evBoth _ Cev _   = decC-no-output {c} Cev

RS-no-input : ∀ {c s a W d id} →
  (decC c ⦀ decS s) ─[ ev (evN (input fz d id) a) ]─► W → ⊥
RS-no-input {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-input {c} Cev
... | evR  _ Sev       = decS-no-input {s} Sev
... | evBoth _ Cev _   = decC-no-input {c} Cev

RS-no-sndmsg : ∀ {c s a W d id} →
  (decC c ⦀ decS s) ─[ ev (evN (sndmsg fz d id) a) ]─► W → ⊥
RS-no-sndmsg {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-sndmsg {c} Cev
... | evR  _ Sev       = decS-no-sndmsg {s} Sev
... | evBoth _ Cev _   = decC-no-sndmsg {c} Cev

RS-no-rcvack : ∀ {c s a W d id} →
  (decC c ⦀ decS s) ─[ ev (evN (rcvack fz d id) a) ]─► W → ⊥
RS-no-rcvack {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-rcvack {c} Cev
... | evR  _ Sev       = decS-no-rcvack {s} Sev
... | evBoth _ Cev _   = decC-no-rcvack {c} Cev

-- Generalized tx-accept classifier: Receiver accepts tx at ANY (d,id).
decC-tx-class-gen : ∀ {c a W d id} →
  decC c ─[ ev (evN (tx fz d id) a) ]─► W →
  (c ≡ Rc0) × (W ≡ succV Receiver (⊤ , tx fz d id) a)
decC-tx-class-gen {Rc0} (sVis refl refl) = refl , refl
decC-tx-class-gen {Rc1} (sVis refl ())
decC-tx-class-gen {Rcg} step = ⊥-elim (decC-Rcg-noev step)

RS-tx-class-gen : ∀ {c s a W d id} →
  (decC c ⦀ decS s) ─[ ev (evN (tx fz d id) a) ]─► W →
  (c ≡ Rc0) × (W ≡ (succV Receiver (⊤ , tx fz d id) a ⦀ decS s))
RS-tx-class-gen {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = proj₁ cl , cong (λ z → z ⦀ decS s) (proj₂ cl)
  where cl = decC-tx-class-gen {c} Cev
... | evR  _ Sev       = ⊥-elim (decS-no-tx {s} Sev)
... | evBoth _ _ Sev   = ⊥-elim (decS-no-tx {s} Sev)

-- decO-output-pins : output is emitted (Op.Output) by decO only at (lo, KA).
decO-output-pins : ∀ {o a W d id} →
  decO o ─[ ev (evN (output′ fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
decO-output-pins {O0} (sVis refl ())
decO-output-pins {O1} {a} {W} {d} {id} (sVis refl br)
  with Net-≟ {⊤} (⊤ , output′ fz lo N2N_KeepAlive) (⊤ , output′ fz d id) | br
... | yes refl | _  = refl , refl
... | no  _    | ()
decO-output-pins {O2} (sVis refl ())
decO-output-pins {Og} step = ⊥-elim (decO-Og-noev step)

-- decS-ack-pins : ack is emitted (Prefix) by SndAck only at (lo, KA).
decS-ack-pins : ∀ {s a W d id} →
  decS s ─[ ev (evN (ack fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
decS-ack-pins {Sa0} (sVis refl ())
decS-ack-pins {Sa1} {a} {W} {d} {id} (sVis refl br)
  with Net-≟ {⊤} (⊤ , ack fz lo N2N_KeepAlive) (⊤ , ack fz d id) | br
... | yes refl | _  = refl , refl
... | no  _    | ()
decS-ack-pins {Sag} step = ⊥-elim (decS-Sag-noev step)

RS-ack-pins : ∀ {c s a W d id} →
  (decC c ⦀ decS s) ─[ ev (evN (ack fz d id) a) ]─► W → (d ≡ lo) × (id ≡ N2N_KeepAlive)
RS-ack-pins {c} {s} step with Par-ev-elim ∅ES ⊤merge (decC c) (decS s) step
... | evSync mem _ _  = ⊥-elim mem
... | evL  _ Cev      = ⊥-elim (decC-no-ack {c} Cev)
... | evR  _ Sev      = decS-ack-pins {s} Sev
... | evBoth _ Cev _  = ⊥-elim (decC-no-ack {c} Cev)

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
  ⊎ ((c ≡ Rc0) × Σ[ d ∈ Dir ] Σ[ id ∈ IDs ]
        (evl (evLabel B e a) ≡ txLbl-at d id)
      × (W ≡ ((decO o) ∥⇘ csRS' ⇙ (succV Receiver (⊤ , tx fz d id) tt ⦀ decS s)) ∖ csRS'))
  ⊎ ((s ≡ Sa1) × (evl (evLabel B e a) ≡ ackLbl)    × (W ≡ decRx o c Sag))
sim-Rx-ev {o} {c} {s} step
  with Hide-ev-elim csRS' ((decO o) ∥⇘ csRS' ⇙ (decC c ⦀ decS s)) step
... | heV {B} {e} {a} _ ¬cs parev with e
-- output: ∉csRS'; decO offers it solo at O1 (pinned to (lo,KA)).
... | output fz d id with d ≟ lo | id ≟ N2N_KeepAlive
...   | yes refl | yes refl with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...     | evSync mem _ _   = ⊥-elim mem
...     | evL  _ Oev       = inj₁ (proj₁ cl , refl ,
            cong (λ z → ((z ∥⇘ csRS' ⇙ (decC c ⦀ decS s)) ∖ csRS')) (proj₂ cl))
  where cl = decO-output-class {o} Oev
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | output fz d id | yes refl | yes refl
      | evR  _ RSev      = ⊥-elim (RS-no-output {c} {s} RSev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | output fz d id | yes refl | yes refl
      | evBoth _ _ RSev  = ⊥-elim (RS-no-output {c} {s} RSev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | output fz d id | no ¬d | _
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (¬d (proj₁ (decO-output-pins {o} Oev)))
...   | evR  _ RSev      = ⊥-elim (RS-no-output {c} {s} RSev)
...   | evBoth _ _ RSev  = ⊥-elim (RS-no-output {c} {s} RSev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | output fz d id | yes refl | no ¬id
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (¬id (proj₂ (decO-output-pins {o} Oev)))
...   | evR  _ RSev      = ⊥-elim (RS-no-output {c} {s} RSev)
...   | evBoth _ _ RSev  = ⊥-elim (RS-no-output {c} {s} RSev)
-- tx: ∉csRS'; Receiver accepts it solo at Rc0 at ANY (d,id).
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx fz d id
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-tx {o} Oev)
...   | evR  _ RSev      = inj₂ (inj₁ (proj₁ cl , d , id , refl ,
            cong (λ z → (((decO o) ∥⇘ csRS' ⇙ z) ∖ csRS')) (proj₂ cl)))
  where cl = RS-tx-class-gen {c} {s} RSev
...   | evBoth _ Oev _   = ⊥-elim (decO-no-tx {o} Oev)
-- ack: ∉csRS'; SndAck emits it solo at Sa1 (pinned to (lo,KA)).
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack fz d id
      with d ≟ lo | id ≟ N2N_KeepAlive
...   | yes refl | yes refl with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...     | evSync mem _ _   = ⊥-elim mem
...     | evL  _ Oev       = ⊥-elim (decO-no-ack {o} Oev)
...     | evR  _ RSev      = inj₂ (inj₂ (proj₁ cl , refl ,
            cong (λ z → (((decO o) ∥⇘ csRS' ⇙ z) ∖ csRS')) (proj₂ cl)))
  where cl = RS-ack-class {c} {s} RSev
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack fz d id | yes refl | yes refl
      | evBoth _ Oev _   = ⊥-elim (decO-no-ack {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack fz d id | no ¬d | _
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-ack {o} Oev)
...   | evR  _ RSev      = ⊥-elim (¬d (proj₁ (RS-ack-pins {c} {s} RSev)))
...   | evBoth _ Oev _   = ⊥-elim (decO-no-ack {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack fz d id | yes refl | no ¬id
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-ack {o} Oev)
...   | evR  _ RSev      = ⊥-elim (¬id (proj₂ (RS-ack-pins {c} {s} RSev)))
...   | evBoth _ Oev _   = ⊥-elim (decO-no-ack {o} Oev)
-- rcvmsg / sndack: ∈csRS', so the hide-passed `¬cs` is `¬ ⊤` ⇒ absurd.
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg l d id′ = ⊥-elim (¬cs Poly.tt)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndack l d id′ = ⊥-elim (¬cs Poly.tt)
-- input / sndmsg / rcvack: neither decO nor RS offers them ⇒ refute.
-- (id-pinned via the IDs split, as for the sync events.)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input fz d id
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-input {o} Oev)
...   | evR  _ RSev      = ⊥-elim (RS-no-input {c} {s} RSev)
...   | evBoth _ Oev _   = ⊥-elim (decO-no-input {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg fz d id
      with Par-ev-elim csRS' ⊤merge (decO o) (decC c ⦀ decS s) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-sndmsg {o} Oev)
...   | evR  _ RSev      = ⊥-elim (RS-no-sndmsg {c} {s} RSev)
...   | evBoth _ Oev _   = ⊥-elim (decO-no-sndmsg {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack fz d id
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

-- Generalized (any d,id) label→membership + label disequalities, for the
-- accept-any drainer disjuncts (Rx tx via Receiver / Tx ack via RcvAck).
txg→mem : ∀ {B} {e : Net ⊤ B} {a} {d id}
        → evl (evLabel B e a) ≡ txLbl-at d id → csTA' .mem (B , e) a
txg→mem refl = Poly.tt
ackg→mem : ∀ {B} {e : Net ⊤ B} {a} {d id}
         → evl (evLabel B e a) ≡ ackLbl-at d id → csTA' .mem (B , e) a
ackg→mem refl = Poly.tt
inputLbl≢txg : ∀ {d id} → inputLbl ≡ txLbl-at d id → ⊥
inputLbl≢txg ()
outputLbl≢ackg : ∀ {d id} → outputLbl ≡ ackLbl-at d id → ⊥
outputLbl≢ackg ()
txg≢ackg : ∀ {d id d′ id′} →
  txLbl-at d id ≡ ackLbl-at d′ id′ → ⊥
txg≢ackg ()

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
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s))) Weq
...   | inj₂ (inj₁ (refl , refl , Weq)) =
        mkCS Ig t Rg o c s , NM.rcvack ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s))) Weq
...   | inj₂ (inj₂ (inj₁ (refl , Weq))) =
        mkCS I0 t r o c s , gI ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s))) Weq
...   | inj₂ (inj₂ (inj₂ (inj₁ (refl , Weq)))) =
        mkCS i T0 r o c s , gT ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s))) Weq
...   | inj₂ (inj₂ (inj₂ (inj₂ (refl , Weq)))) =
        mkCS i t R0 o c s , gR ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s))) Weq
sim-modA (mkCS i t r o c s) (maτ parτ)
  | τR Q′ Rxτ refl with sim-Rx-τ {o} {c} {s} Rxτ
...   | inj₁ (refl , refl , Weq) =
        mkCS i t r O1 Rcg s , NM.rcvmsg ,
        cong (λ z → ((decTx i t r) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₁ (refl , refl , Weq)) =
        mkCS i t r Og c Sa1 , NM.sndack ,
        cong (λ z → ((decTx i t r) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₂ (inj₁ (refl , Weq))) =
        mkCS i t r O0 c s , gO ,
        cong (λ z → ((decTx i t r) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₂ (inj₂ (inj₁ (refl , Weq)))) =
        mkCS i t r o Rc0 s , gRc ,
        cong (λ z → ((decTx i t r) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₂ (inj₂ (inj₂ (refl , Weq)))) =
        mkCS i t r o c Sa0 , gSa ,
        cong (λ z → ((decTx i t r) ∥⇘ csTA' ⇙ z)) Weq
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
...   | inj₁ (_ , Lin , _) | inj₂ (inj₁ (_ , _ , _ , Ltx , _)) =
          ⊥-elim (inputLbl≢txg (trans (sym Lin) Ltx))
...   | inj₁ (_ , Lin , _) | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (inputLbl≢ackLbl (trans (sym Lin) Lack))
-- Tx = tx: consistent only with Rx = tx ⇒ `⇒ᵢ tx`.
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₁ (_ , Lout , _) =
          ⊥-elim (outputLbl≢txLbl (trans (sym Lout) Ltx))
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (txLbl≢ackLbl (trans (sym Ltx) Lack))
sim-modA (mkCS i t r o c s) (maE mem parev) | evSync _ Txev Rxev
  | inj₂ (inj₂ (refl , dT , idT , Lack , _)) | inj₁ (_ , Lout , _) =
          ⊥-elim (outputLbl≢ackg (trans (sym Lout) Lack))
sim-modA (mkCS i t r o c s) (maE mem parev) | evSync _ Txev Rxev
  | inj₂ (inj₂ (refl , dT , idT , Lack , _)) | inj₂ (inj₁ (_ , _ , _ , Ltx , _)) =
          ⊥-elim (txg≢ackg (trans (sym Ltx) Lack))
-- tx SYNC: Tx emits tx (pinned lo,KA), Rx accepts at (dR,idR) ⇒ pin & build.
sim-modA (mkCS i t r o c s) (maE mem parev) | evSync _ Txev Rxev
  | inj₂ (inj₁ (refl , Ltx , refl)) | inj₂ (inj₁ (refl , dR , idR , LtxR , WeqR))
      with trans (sym LtxR) Ltx
... | refl = mkCS i Tg r o Rc1 s , NM.tx ,
      cong (λ w → (decTx i Tg r) ∥⇘ csTA' ⇙ w) WeqR
-- ack SYNC: Rx emits ack (pinned lo,KA), Tx accepts at (dT,idT) ⇒ pin & build.
sim-modA (mkCS i t r o c s) (maE mem parev) | evSync _ Txev Rxev
  | inj₂ (inj₂ (refl , dT , idT , LackT , WeqT)) | inj₂ (inj₂ (refl , Lack , refl))
      with trans (sym LackT) Lack
... | refl = mkCS i t R1 o c Sag , NM.ack ,
      cong (λ z → z ∥⇘ csTA' ⇙ (decRx o c Sag)) WeqT

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
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s))) Weq
...   | inj₂ (inj₁ (_ , Ltx  , _)) = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , _ , _ , Lack , _)) = ⊥-elim (¬cs (ackg→mem Lack))
-- a SOLO Rx-side offer (∉csTA): must be `output`.
sim-uVis (mkCS i t r o c s) ¬cs st
  | evR _ Rxev with sim-Rx-ev {o} {c} {s} Rxev
...   | inj₁ (refl , _ , Weq) =
        mkCS i t r O2 c s , NM.output ,
        cong (λ z → ((decTx i t r) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₁ (_ , _ , _ , Ltx  , _)) = ⊥-elim (¬cs (txg→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) = ⊥-elim (¬cs (ackLbl→mem Lack))
-- a SYNC: the synced event is in csTA', contradicting `¬cs`.
sim-uVis (mkCS i t r o c s) ¬cs st | evSync mem _ _ = ⊥-elim (¬cs mem)
-- both-solo (∉csTA): Tx can only offer `input`, Rx only `output`;
--   their shared label can't be both ⇒ ⊥ (and tx/ack contradict `¬cs`).
sim-uVis (mkCS i t r o c s) ¬cs st
  | evBoth _ Txev Rxev with sim-Tx-ev {i} {t} {r} Txev | sim-Rx-ev {o} {c} {s} Rxev
...   | inj₁ (_ , Lin , _)        | inj₁ (_ , Lout , _) =
          ⊥-elim (inputLbl≢outputLbl (trans (sym Lin) Lout))
...   | inj₁ (_ , Lin , _)        | inj₂ (inj₁ (_ , _ , _ , Ltx , _)) =
          ⊥-elim (inputLbl≢txg (trans (sym Lin) Ltx))
...   | inj₁ (_ , Lin , _)        | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (inputLbl≢ackLbl (trans (sym Lin) Lack))
...   | inj₂ (inj₁ (_ , Ltx , _)) | _ = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , _ , _ , Lack , _)) | _ = ⊥-elim (¬cs (ackg→mem Lack))

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

------------------------------------------------------------------------
-- MILESTONE 3 (reverse): `Network ⊑D CopySpec`.
--
-- `Network ⊑D CopySpec = ∀{s} → divergences CopySpec s → divergences Network s`.
-- `CopySpec` is divergence-free along EVERY trace, so `divergences CopySpec`
-- is empty and the inclusion is vacuous.
--
-- `CopySpec` (instance p1) = `⦀⋆ (map CopysId allIDs)` with ONE live leaf
-- `Copy fz lo N2N_KeepAlive` (the other ids give `⦀Fin 0 = Skip`, inert).  Its
-- lifecycle is exactly three reachable states — NO hiding, NO sync, NO
-- diamonds:
--   C0 = CopySpec  — offers `input` only, τ-stable; `input` → C1.
--   C1             — offers `output` only, τ-stable; `output` → Cg.
--   Cg             — the post-`output` loop0 restart guard; ONE τ → C0
--                    (definitionally C0 = CopySpec), offers NO visible event.
------------------------------------------------------------------------

-- The three reachable states, defined by reduction off `CopySpec`.
C0 C1 Cg : NetProc
C0 = CopySpec
C1 = succV C0 inputAt tt
Cg = succV C1 outputAt tt

-- Sanity probes (definitional, by `refl`).
C0-offers-input : is-just (vis-of (force C0) inputAt tt) ≡ true
C0-offers-input = refl

C0-no-output : vis-of (force C0) outputAt tt ≡ nothing
C0-no-output = refl

C1-offers-output : is-just (vis-of (force C1) outputAt tt) ≡ true
C1-offers-output = refl

C1-no-input : vis-of (force C1) inputAt tt ≡ nothing
C1-no-input = refl

Cg-no-input : vis-of (force Cg) inputAt tt ≡ nothing
Cg-no-input = refl

Cg-no-output : vis-of (force Cg) outputAt tt ≡ nothing
Cg-no-output = refl

-- Step characterizations.
-- C0 is τ-stable (= `CopySpec-stable`).
C0-noτ : ∀ {W} → C0 ─[ τ ]─► W → ⊥
C0-noτ = CopySpec-stable

-- C1 is τ-stable (mid-state, only a visible `output` offer; no enabled τ).
C1-noτ : ∀ {W} → C1 ─[ τ ]─► W → ⊥
C1-noτ (sSil ())
C1-noτ (sTau {i = _ , fin}                       refl ())
C1-noτ (sTau {i = _ , base _}                    refl ())
C1-noτ (sTau {i = _ , pair fin (base _)}         refl ())
C1-noτ (sTau {i = _ , pair fin fin}              refl ())
C1-noτ (sTau {i = _ , pair fin (pair _ _)}       refl ())
C1-noτ (sTau {i = _ , pair (base _) _}           refl ())
C1-noτ (sTau {i = _ , pair (pair _ _) _}         refl ())

-- Cg has the single restart-guard τ to C0 (a `sSil refl`, like the decI/decO
-- guards); no other τ.
Cg-τ : ∀ {W} → Cg ─[ τ ]─► W → W ≡ C0
Cg-τ (sSil refl) = refl
Cg-τ (sTau () _)

-- Cg (the restart guard) offers NO visible event (mirror `decI-Ig-noev`).
Cg-noev : ∀ {B} {e : Net ⊤ B} {a} {W} →
  Cg ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
Cg-noev (sVis () _)

-- Skip (= Ret tt) offers no visible event: a `sVis` needs `force Skip ≡
-- react …`, but `force Skip = ret tt`.
Skip-no-ev : ∀ {B} {e : Net ⊤ B} {a} {W} →
  Skip {0ℓ} ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
Skip-no-ev (sVis () _)

------------------------------------------------------------------------
-- Interleave peeling: `CopySpec` is `⦀⋆ (map CopysId allIDs)`, a nest of
-- `_⦀_` (= `Par ∅ES ⊤merge`) whose only live operand is `Copy KA c0`; every
-- other operand is `Skip` (`numConns id = 0 ⇒ ⦀Fin 0 = Skip`, and the empty
-- `⦀⋆ [] = Skip`).  We peel visible steps through the inert (`NoEv`) Skips.
------------------------------------------------------------------------

-- `P` offers no visible event.
NoEv : NetProc → Set₁
NoEv P = ∀ {B} {e : Net ⊤ B} {a} {W} →
         P ─[ ev (evl (evLabel B e a)) ]─► W → ⊥

-- `_⦀_` of two `NoEv` operands is `NoEv` (no sync in `∅ES`; solos/both
-- delegate to an operand step, both refuted).
⦀-NoEv : ∀ {P Q} → NoEv P → NoEv Q → NoEv (P ⦀ Q)
⦀-NoEv {P} {Q} nP nQ st with Par-ev-elim ∅ES ⊤merge P Q st
... | evSync () _ _
... | evL  _ pst     = nP pst
... | evR  _ qst     = nQ qst
... | evBoth _ pst _ = nP pst

-- The five inert `CopysId`s reduce to `Skip` (numConns = 0).
-- (old per-id CopysId / CopySpec-layout sanity lemmas removed: the config-driven
-- medium has no per-id operand; C0/C1/Cg below are succV-based and nesting-robust.)

-- Live-leaf characterization.  `Copy KA c0`'s offer map fires ONLY
-- `input KA c0`, landing on its input-successor (= `Output(KA,c0) tt Skip`).
CopyLeaf : NetProc
CopyLeaf = Copy fz lo N2N_KeepAlive

CopyLeaf-in : NetProc
CopyLeaf-in = succV CopyLeaf inputAt tt
CopyLeaf-ev : ∀ {B} {e : Net ⊤ B} {a} {W} →
  CopyLeaf ─[ ev (evl (evLabel B e a)) ]─► W → W ≡ CopyLeaf-in
CopyLeaf-ev {e = input fz lo N2N_KeepAlive}    (sVis refl refl) = refl
CopyLeaf-ev {e = input fz lo N2N_ChainSync} (sVis refl ())
CopyLeaf-ev {e = input fz lo N2N_BlockFetch} (sVis refl ())
CopyLeaf-ev {e = input fz lo N2N_TxSubmission} (sVis refl ())
CopyLeaf-ev {e = input fz lo N2N_LeiosNotify} (sVis refl ())
CopyLeaf-ev {e = input fz lo N2N_LeiosFetch} (sVis refl ())
CopyLeaf-ev {e = input fz hi id} (sVis refl ())
CopyLeaf-ev {e = output l d id} (sVis refl ())
CopyLeaf-ev {e = sndmsg l d id} (sVis refl ())
CopyLeaf-ev {e = rcvmsg l d id} (sVis refl ())
CopyLeaf-ev {e = tx l d id} (sVis refl ())
CopyLeaf-ev {e = sndack l d id} (sVis refl ())
CopyLeaf-ev {e = rcvack l d id} (sVis refl ())
CopyLeaf-ev {e = ack l d id} (sVis refl ())

-- Label-pinned: the fired label is exactly `inputLbl`.
CopyLeaf-evL : ∀ {B} {e : Net ⊤ B} {a} {W} →
  CopyLeaf ─[ ev (evl (evLabel B e a)) ]─► W → evl (evLabel B e a) ≡ inputLbl
CopyLeaf-evL {e = input fz lo N2N_KeepAlive}    (sVis refl refl) = refl
CopyLeaf-evL {e = input fz lo N2N_ChainSync} (sVis refl ())
CopyLeaf-evL {e = input fz lo N2N_BlockFetch} (sVis refl ())
CopyLeaf-evL {e = input fz lo N2N_TxSubmission} (sVis refl ())
CopyLeaf-evL {e = input fz lo N2N_LeiosNotify} (sVis refl ())
CopyLeaf-evL {e = input fz lo N2N_LeiosFetch} (sVis refl ())
CopyLeaf-evL {e = input fz hi id} (sVis refl ())
CopyLeaf-evL {e = output l d id} (sVis refl ())
CopyLeaf-evL {e = sndmsg l d id} (sVis refl ())
CopyLeaf-evL {e = rcvmsg l d id} (sVis refl ())
CopyLeaf-evL {e = tx l d id} (sVis refl ())
CopyLeaf-evL {e = sndack l d id} (sVis refl ())
CopyLeaf-evL {e = rcvack l d id} (sVis refl ())
CopyLeaf-evL {e = ack l d id} (sVis refl ())

-- A visible step of `P ⦀ Q` with `Q` inert (`NoEv`) is a solo step of `P`,
-- and the residual is `P′ ⦀ Q`.
⦀-ev-left : ∀ {P Q B} {e : Net ⊤ B} {a} {W} → NoEv Q →
  (P ⦀ Q) ─[ ev (evl (evLabel B e a)) ]─► W →
  Σ[ P′ ∈ NetProc ] ((P ─[ ev (evl (evLabel B e a)) ]─► P′) × (W ≡ (P′ ⦀ Q)))
⦀-ev-left {P} {Q} nQ st with Par-ev-elim ∅ES ⊤merge P Q st
... | evSync () _ _
... | evL  _ pst      = _ , pst , refl
... | evR  _ qst      = ⊥-elim (nQ qst)
... | evBoth _ _ qst  = ⊥-elim (nQ qst)

-- Symmetric: with `P` inert, a visible step of `P ⦀ Q` is a solo of `Q`.
⦀-ev-right : ∀ {P Q B} {e : Net ⊤ B} {a} {W} → NoEv P →
  (P ⦀ Q) ─[ ev (evl (evLabel B e a)) ]─► W →
  Σ[ Q′ ∈ NetProc ] ((Q ─[ ev (evl (evLabel B e a)) ]─► Q′) × (W ≡ (P ⦀ Q′)))
⦀-ev-right {P} {Q} nP st with Par-ev-elim ∅ES ⊤merge P Q st
... | evSync () _ _
... | evL  _ pst      = ⊥-elim (nP pst)
... | evR  _ qst      = _ , qst , refl
... | evBoth _ pst _  = ⊥-elim (nP pst)

-- Inert (NoEv) building blocks.
Skip0-NoEv : NoEv (Skip {0ℓ})
Skip0-NoEv = Skip-no-ev

-- The post-KeepAlive tail `Skip ⦀ (Skip ⦀ Skip)` is inert.
tail-NoEv : NoEv (Skip {0ℓ} ⦀ (Skip {0ℓ} ⦀ Skip {0ℓ}))
tail-NoEv = ⦀-NoEv Skip0-NoEv (⦀-NoEv Skip0-NoEv Skip0-NoEv)

-- C1 is the input-successor laid out: the live leaf advanced to its
-- input-successor, every Skip unchanged.
C1-layout :
  C1 ≡ ((CopyLeaf-in ⦀ Skip {0ℓ}) ⦀ Skip {0ℓ})
C1-layout = refl

-- C0 fires ONLY `input`, landing on C1.  Peel the three leading Skips
-- (`⦀-ev-right`), the trailing tail (`⦀-ev-left`), and the right Skip of the
-- KeepAlive operand (`⦀-ev-left`), down to the live `Copy KA c0` leaf
-- (`CopyLeaf-ev`); each residual reassembles definitionally to `C1`.
C0-ev : ∀ {B} {e : Net ⊤ B} {a} {W} →
  C0 ─[ ev (evl (evLabel B e a)) ]─► W → W ≡ C1
C0-ev st
  with ⦀-ev-left Skip0-NoEv st
... | _ , st1 , refl
  with ⦀-ev-left Skip0-NoEv st1
... | _ , st2 , refl
  with CopyLeaf-ev st2
... | refl = refl

-- The live leaf after `input`: `CopyLeaf-in` fires ONLY `output`, landing on
-- its output-successor.
CopyLeaf-g : NetProc
CopyLeaf-g = succV CopyLeaf-in outputAt tt

CopyLeaf-in-ev : ∀ {B} {e : Net ⊤ B} {a} {W} →
  CopyLeaf-in ─[ ev (evl (evLabel B e a)) ]─► W → W ≡ CopyLeaf-g
CopyLeaf-in-ev {e = output fz lo N2N_KeepAlive}     (sVis refl refl) = refl
CopyLeaf-in-ev {e = output fz lo N2N_ChainSync}    (sVis refl ())
CopyLeaf-in-ev {e = output fz lo N2N_BlockFetch}   (sVis refl ())
CopyLeaf-in-ev {e = output fz lo N2N_TxSubmission} (sVis refl ())
CopyLeaf-in-ev {e = output fz lo N2N_LeiosNotify}  (sVis refl ())
CopyLeaf-in-ev {e = output fz lo N2N_LeiosFetch}   (sVis refl ())
CopyLeaf-in-ev {e = output fz hi id}               (sVis refl ())
CopyLeaf-in-ev {e = input l d id}                   (sVis refl ())
CopyLeaf-in-ev {e = sndmsg l d id}                   (sVis refl ())
CopyLeaf-in-ev {e = rcvmsg l d id}                   (sVis refl ())
CopyLeaf-in-ev {e = tx l d id}                   (sVis refl ())
CopyLeaf-in-ev {e = sndack l d id}                   (sVis refl ())
CopyLeaf-in-ev {e = rcvack l d id}                   (sVis refl ())
CopyLeaf-in-ev {e = ack l d id}                   (sVis refl ())

-- Label-pinned: the fired label is exactly `outputLbl`.
CopyLeaf-in-evL : ∀ {B} {e : Net ⊤ B} {a} {W} →
  CopyLeaf-in ─[ ev (evl (evLabel B e a)) ]─► W → evl (evLabel B e a) ≡ outputLbl
CopyLeaf-in-evL {e = output fz lo N2N_KeepAlive}     (sVis refl refl) = refl
CopyLeaf-in-evL {e = output fz lo N2N_ChainSync}    (sVis refl ())
CopyLeaf-in-evL {e = output fz lo N2N_BlockFetch}   (sVis refl ())
CopyLeaf-in-evL {e = output fz lo N2N_TxSubmission} (sVis refl ())
CopyLeaf-in-evL {e = output fz lo N2N_LeiosNotify}  (sVis refl ())
CopyLeaf-in-evL {e = output fz lo N2N_LeiosFetch}   (sVis refl ())
CopyLeaf-in-evL {e = output fz hi id}               (sVis refl ())
CopyLeaf-in-evL {e = input l d id}                   (sVis refl ())
CopyLeaf-in-evL {e = sndmsg l d id}                   (sVis refl ())
CopyLeaf-in-evL {e = rcvmsg l d id}                   (sVis refl ())
CopyLeaf-in-evL {e = tx l d id}                   (sVis refl ())
CopyLeaf-in-evL {e = sndack l d id}                   (sVis refl ())
CopyLeaf-in-evL {e = rcvack l d id}                   (sVis refl ())
CopyLeaf-in-evL {e = ack l d id}                   (sVis refl ())

-- Cg laid out: the live leaf advanced to its output-successor, Skips fixed.
Cg-layout :
  Cg ≡ ((CopyLeaf-g ⦀ Skip {0ℓ}) ⦀ Skip {0ℓ})
Cg-layout = refl

-- C1 fires ONLY `output`, landing on Cg.  Same peel as C0-ev.
C1-ev : ∀ {B} {e : Net ⊤ B} {a} {W} →
  C1 ─[ ev (evl (evLabel B e a)) ]─► W → W ≡ Cg
C1-ev st
  with ⦀-ev-left Skip0-NoEv st
... | _ , st1 , refl
  with ⦀-ev-left Skip0-NoEv st1
... | _ , st2 , refl
  with CopyLeaf-in-ev st2
... | refl = refl

-- Label-pinned C0 / C1 visible steps (label = input/output, residual = C1/Cg).
C0-evL : ∀ {B} {e : Net ⊤ B} {a} {W} →
  C0 ─[ ev (evl (evLabel B e a)) ]─► W → (evl (evLabel B e a) ≡ inputLbl) × (W ≡ C1)
C0-evL st
  with ⦀-ev-left Skip0-NoEv st
... | _ , st1 , refl with ⦀-ev-left Skip0-NoEv st1
... | _ , st2 , refl with CopyLeaf-evL st2 | CopyLeaf-ev st2
... | refl | refl = refl , refl

C1-evL : ∀ {B} {e : Net ⊤ B} {a} {W} →
  C1 ─[ ev (evl (evLabel B e a)) ]─► W → (evl (evLabel B e a) ≡ outputLbl) × (W ≡ Cg)
C1-evL st
  with ⦀-ev-left Skip0-NoEv st
... | _ , st1 , refl with ⦀-ev-left Skip0-NoEv st1
... | _ , st2 , refl with CopyLeaf-in-evL st2 | CopyLeaf-in-ev st2
... | refl | refl = refl , refl

-- The three CopySpec lifecycle STRONG steps (intros for the builder).
C0─input─►C1 : C0 ─[ ev inputLbl ]─► C1
C0─input─►C1 = sVis {at = inputAt} refl refl

C1─output─►Cg : C1 ─[ ev outputLbl ]─► Cg
C1─output─►Cg = sVis {at = outputAt} refl refl

Cg─τ─►C0 : Cg ─[ τ ]─► C0
Cg─τ─►C0 = sSil refl

------------------------------------------------------------------------
-- ¬ Diverges at each state, then the coinductive `GoodC` invariant.
------------------------------------------------------------------------

¬Div-C0 : ¬ Diverges C0
¬Div-C0 = ¬Diverges-CopySpec

¬Div-C1 : ¬ Diverges C1
¬Div-C1 d = C1-noτ (d .Diverges.step)

¬Div-Cg : ¬ Diverges Cg
¬Div-Cg d = ¬Div-C0 (subst Diverges (Cg-τ (d .Diverges.step)) (d .Diverges.rest))


-- Coinductive divergence-freedom invariant.  `gcev` is stated for ANY
-- `ev e` (an `evl` visible event OR a `√` termination), so the reach-walk can
-- consume any `⟹-ev`.
record GoodC (W : NetProc) : Set₁ where
  coinductive
  field
    gcnd : ¬ Diverges W
    gcτ  : ∀ {W′} → W ─[ τ ]─► W′ → GoodC W′
    gcev : ∀ {W′} {e : Event√ NetR} → W ─[ ev e ]─► W′ → GoodC W′
open GoodC

goodC-C0 : GoodC C0
goodC-C1 : GoodC C1
goodC-Cg : GoodC Cg

-- A `√` step lands on `deadlock` (inert); an `evl` step is routed by the
-- per-state event characterization.  `with`-matching the `≡`-lemma to `refl`
-- keeps the corecursive call directly under the copattern (productive),
-- mirroring `goodU-cs`/`goodU-next` of MILESTONE 2.
goodC-C0 .gcnd                  = ¬Div-C0
goodC-C0 .gcτ  st               = ⊥-elim (C0-noτ st)
goodC-C0 .gcev {e = √ x}    (sRet ())
goodC-C0 .gcev {e = evl _} st  with C0-ev st
... | refl                      = goodC-C1

goodC-C1 .gcnd                  = ¬Div-C1
goodC-C1 .gcτ  st               = ⊥-elim (C1-noτ st)
goodC-C1 .gcev {e = √ x}    (sRet ())
goodC-C1 .gcev {e = evl _} st  with C1-ev st
... | refl                      = goodC-Cg

goodC-Cg .gcnd                  = ¬Div-Cg
goodC-Cg .gcτ  st               with Cg-τ st
... | refl                      = goodC-C0
goodC-Cg .gcev {e = √ x}    (sRet ())
goodC-Cg .gcev {e = evl _} st  = ⊥-elim (Cg-noev st)

------------------------------------------------------------------------
-- No weakly-reachable state of CopySpec diverges, hence `divergences
-- CopySpec` is empty and `Network ⊑D CopySpec` is vacuous.
------------------------------------------------------------------------

copy-reach-noDiv : ∀ {s W} → CopySpec ⟹⟨ s ⟩ W → ¬ Diverges W
copy-reach-noDiv = go goodC-C0
  where
  go : ∀ {s W W′} → GoodC W → W ⟹⟨ s ⟩ W′ → ¬ Diverges W′
  go g ⟹-refl         = g .gcnd
  go g (⟹-τ  st rest) = go (g .gcτ  st) rest
  go g (⟹-ev st rest) = go (g .gcev st) rest

-- THE REVERSE DIVERGENCE REFINEMENT.
--   `Network ⊑D CopySpec = ∀{s} → divergences CopySpec s → divergences
--   Network s`.  `divergences CopySpec s` carries a weakly-reachable witness
--   `W` with `Diverges W`; `copy-reach-noDiv` rules every such `W` out, so the
--   inclusion is vacuous.
Network⊑D-CopySpec : Network ⊑D CopySpec
Network⊑D-CopySpec div =
  ⊥-elim (copy-reach-noDiv (IsDivergence.reach div) (IsDivergence.divwit div))

------------------------------------------------------------------------
-- D1: SINGLE-STEP BISIMULATION  Network ↔ the abstract CS-automaton.
--
-- `⟦_⟧N := ⟦_⟧ ∖ csTA'` decodes each abstract state to the corresponding
-- Network state.  We show (both directions, single step):
--   ⇒ᵢ  ↔  Network-τ        (internal, hidden)
--   ⇒ᵥ  ↔  Network-visible   (input / output)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- D1.1: the hidden decode and its initial agreement with Network.
------------------------------------------------------------------------

⟦_⟧N : CS → NetProc
⟦ cs ⟧N = ⟦ cs ⟧ ∖ csTA'

decN-cs0 : ⟦ cs0 ⟧N ≡ Network
decN-cs0 = refl

------------------------------------------------------------------------
-- D1' : the CONVERSE simulation for the ABSTRACT decode `⟦_⟧N`.
--
--   real-⇒ᵢ-Net : cs ⇒ᵢ cs′ → ⟦ cs ⟧N ─[ τ ]─► ⟦ cs′ ⟧N
--   real-⇒ᵥ-Net : cs ⇒ᵥ cs′ → Σ l. ⟦ cs ⟧N ─[ ev l ]─► ⟦ cs′ ⟧N
--
-- Every abstract step is realised by lifting the active leaf's concrete
-- LTS step (sVis/sSil) through the ⦀ / Par⊤ / ∖ layers via the
-- Par-τ-L/R, Par-soloL/R, Par-sync, Hide-τ/keep/hidden tools.
------------------------------------------------------------------------

-- viewV-non-offer helpers (the idle operands at each solo lift).
-- Each is case-split over the partner's positions; bare `refl` per case.

-- single-leaf non-offers (for the inner ⦀ solos).
nR-sndmsg : ∀ r → viewV (PTree.force (decR r)) (⊤ , sndmsg fz lo N2N_KeepAlive) tt ≡ nothing
nR-sndmsg R0 = refl
nR-sndmsg R1 = refl
nR-sndmsg Rg = refl

nT-rcvack : ∀ t → viewV (PTree.force (decT t)) (⊤ , rcvack fz lo N2N_KeepAlive) tt ≡ nothing
nT-rcvack T0 = refl
nT-rcvack T1 = refl
nT-rcvack Tg = refl

nS-rcvmsg : ∀ s → viewV (PTree.force (decS s)) (⊤ , rcvmsg fz lo N2N_KeepAlive) tt ≡ nothing
nS-rcvmsg Sa0 = refl
nS-rcvmsg Sa1 = refl
nS-rcvmsg Sag = refl

nC-sndack : ∀ c → viewV (PTree.force (decC c)) (⊤ , sndack fz lo N2N_KeepAlive) tt ≡ nothing
nC-sndack Rc0 = refl
nC-sndack Rc1 = refl
nC-sndack Rcg = refl

-- single-leaf non-offers of tx / ack (for the top-sync solos).
nR-tx : ∀ r → viewV (PTree.force (decR r)) (⊤ , tx fz lo N2N_KeepAlive) tt ≡ nothing
nR-tx R0 = refl
nR-tx R1 = refl
nR-tx Rg = refl

nI-tx : ∀ i → viewV (PTree.force (decI i)) (⊤ , tx fz lo N2N_KeepAlive) tt ≡ nothing
nI-tx I0 = refl
nI-tx I1 = refl
nI-tx I2 = refl
nI-tx Ig = refl

nS-tx : ∀ s → viewV (PTree.force (decS s)) (⊤ , tx fz lo N2N_KeepAlive) tt ≡ nothing
nS-tx Sa0 = refl
nS-tx Sa1 = refl
nS-tx Sag = refl

nO-tx : ∀ o → viewV (PTree.force (decO o)) (⊤ , tx fz lo N2N_KeepAlive) tt ≡ nothing
nO-tx O0 = refl
nO-tx O1 = refl
nO-tx O2 = refl
nO-tx Og = refl

nT-ack : ∀ t → viewV (PTree.force (decT t)) (⊤ , ack fz lo N2N_KeepAlive) tt ≡ nothing
nT-ack T0 = refl
nT-ack T1 = refl
nT-ack Tg = refl

nI-ack : ∀ i → viewV (PTree.force (decI i)) (⊤ , ack fz lo N2N_KeepAlive) tt ≡ nothing
nI-ack I0 = refl
nI-ack I1 = refl
nI-ack I2 = refl
nI-ack Ig = refl

nC-ack : ∀ c → viewV (PTree.force (decC c)) (⊤ , ack fz lo N2N_KeepAlive) tt ≡ nothing
nC-ack Rc0 = refl
nC-ack Rc1 = refl
nC-ack Rcg = refl

nO-ack : ∀ o → viewV (PTree.force (decO o)) (⊤ , ack fz lo N2N_KeepAlive) tt ≡ nothing
nO-ack O0 = refl
nO-ack O1 = refl
nO-ack O2 = refl
nO-ack Og = refl

-- composite ⦀ non-offers of input / output (for the visible solos).
nTR-input : ∀ t r → viewV (PTree.force (decT t ⦀ decR r)) (⊤ , input fz lo N2N_KeepAlive) tt ≡ nothing
nTR-input T0 R0 = refl
nTR-input T0 R1 = refl
nTR-input T0 Rg = refl
nTR-input T1 R0 = refl
nTR-input T1 R1 = refl
nTR-input T1 Rg = refl
nTR-input Tg R0 = refl
nTR-input Tg R1 = refl
nTR-input Tg Rg = refl

nCS-output : ∀ c s → viewV (PTree.force (decC c ⦀ decS s)) (⊤ , output′ fz lo N2N_KeepAlive) tt ≡ nothing
nCS-output Rc0 Sa0 = refl
nCS-output Rc0 Sa1 = refl
nCS-output Rc0 Sag = refl
nCS-output Rc1 Sa0 = refl
nCS-output Rc1 Sa1 = refl
nCS-output Rc1 Sag = refl
nCS-output Rcg Sa0 = refl
nCS-output Rcg Sa1 = refl
nCS-output Rcg Sag = refl

-- composite Par⊤/∖ side non-offers of input / output (top-level visible solos).
nRx-input : ∀ o c s → viewV (PTree.force (decRx o c s)) (⊤ , input fz lo N2N_KeepAlive) tt ≡ nothing
nRx-input O0 Rc0 Sa0 = refl
nRx-input O0 Rc0 Sa1 = refl
nRx-input O0 Rc0 Sag = refl
nRx-input O0 Rc1 Sa0 = refl
nRx-input O0 Rc1 Sa1 = refl
nRx-input O0 Rc1 Sag = refl
nRx-input O0 Rcg Sa0 = refl
nRx-input O0 Rcg Sa1 = refl
nRx-input O0 Rcg Sag = refl
nRx-input O1 Rc0 Sa0 = refl
nRx-input O1 Rc0 Sa1 = refl
nRx-input O1 Rc0 Sag = refl
nRx-input O1 Rc1 Sa0 = refl
nRx-input O1 Rc1 Sa1 = refl
nRx-input O1 Rc1 Sag = refl
nRx-input O1 Rcg Sa0 = refl
nRx-input O1 Rcg Sa1 = refl
nRx-input O1 Rcg Sag = refl
nRx-input O2 Rc0 Sa0 = refl
nRx-input O2 Rc0 Sa1 = refl
nRx-input O2 Rc0 Sag = refl
nRx-input O2 Rc1 Sa0 = refl
nRx-input O2 Rc1 Sa1 = refl
nRx-input O2 Rc1 Sag = refl
nRx-input O2 Rcg Sa0 = refl
nRx-input O2 Rcg Sa1 = refl
nRx-input O2 Rcg Sag = refl
nRx-input Og Rc0 Sa0 = refl
nRx-input Og Rc0 Sa1 = refl
nRx-input Og Rc0 Sag = refl
nRx-input Og Rc1 Sa0 = refl
nRx-input Og Rc1 Sa1 = refl
nRx-input Og Rc1 Sag = refl
nRx-input Og Rcg Sa0 = refl
nRx-input Og Rcg Sa1 = refl
nRx-input Og Rcg Sag = refl

nTx-output : ∀ i t r → viewV (PTree.force (decTx i t r)) (⊤ , output′ fz lo N2N_KeepAlive) tt ≡ nothing
nTx-output I0 T0 R0 = refl
nTx-output I0 T0 R1 = refl
nTx-output I0 T0 Rg = refl
nTx-output I0 T1 R0 = refl
nTx-output I0 T1 R1 = refl
nTx-output I0 T1 Rg = refl
nTx-output I0 Tg R0 = refl
nTx-output I0 Tg R1 = refl
nTx-output I0 Tg Rg = refl
nTx-output I1 T0 R0 = refl
nTx-output I1 T0 R1 = refl
nTx-output I1 T0 Rg = refl
nTx-output I1 T1 R0 = refl
nTx-output I1 T1 R1 = refl
nTx-output I1 T1 Rg = refl
nTx-output I1 Tg R0 = refl
nTx-output I1 Tg R1 = refl
nTx-output I1 Tg Rg = refl
nTx-output I2 T0 R0 = refl
nTx-output I2 T0 R1 = refl
nTx-output I2 T0 Rg = refl
nTx-output I2 T1 R0 = refl
nTx-output I2 T1 R1 = refl
nTx-output I2 T1 Rg = refl
nTx-output I2 Tg R0 = refl
nTx-output I2 Tg R1 = refl
nTx-output I2 Tg Rg = refl
nTx-output Ig T0 R0 = refl
nTx-output Ig T0 R1 = refl
nTx-output Ig T0 Rg = refl
nTx-output Ig T1 R0 = refl
nTx-output Ig T1 R1 = refl
nTx-output Ig T1 Rg = refl
nTx-output Ig Tg R0 = refl
nTx-output Ig Tg R1 = refl
nTx-output Ig Tg Rg = refl

------------------------------------------------------------------------
-- D1'.A : the internal converse simulation  cs ⇒ᵢ cs′ → ⟦cs⟧N ─[τ]→ ⟦cs′⟧N.
------------------------------------------------------------------------

real-⇒ᵢ-Net : ∀ {cs cs′} → cs NM.⇒ᵢ cs′ → ⟦ cs ⟧N ─[ τ ]─► ⟦ cs′ ⟧N

-- INNER SYNC: sndmsg  (decI I1→I2 ∥ decT T0→T1 solo past decR; ∈ csSR').
real-⇒ᵢ-Net (NM.sndmsg {r} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx I1 T0 r) (decRx o c s)
     (Hide-hidden csSR' _ Poly.tt
       (Par-sync csSR' ⊤merge (decI I1) (decT T0 ⦀ decR r) Poly.tt
         (sVis refl refl)
         (Par-soloL ∅ES ⊤merge (decT T0) (decR r) (λ ()) (sVis refl refl)
           (nR-sndmsg r)))))

-- TOP SYNC: tx  (decT T1→Tg solo to decTx-level ∥ decC Rc0→Rc1 solo to decRx-level; ∈ csTA').
real-⇒ᵢ-Net (NM.tx {i} {r} {o} {s}) =
  Hide-hidden csTA' _ Poly.tt
   (Par-sync csTA' ⊤merge (decTx i T1 r) (decRx o Rc0 s) Poly.tt
     (Hide-keep csSR' _ (λ ())
       (Par-soloR csSR' ⊤merge (decI i) (decT T1 ⦀ decR r) (λ ())
         (Par-soloL ∅ES ⊤merge (decT T1) (decR r) (λ ()) (sVis refl refl)
           (nR-tx r))
         (nI-tx i)))
     (Hide-keep csRS' _ (λ ())
       (Par-soloR csRS' ⊤merge (decO o) (decC Rc0 ⦀ decS s) (λ ())
         (Par-soloL ∅ES ⊤merge (decC Rc0) (decS s) (λ ()) (sVis refl refl)
           (nS-tx s))
         (nO-tx o))))

-- INNER SYNC: rcvmsg  (decO O0→O1 ∥ decC Rc1→Rcg solo past decS; ∈ csRS').
real-⇒ᵢ-Net (NM.rcvmsg {i} {t} {r} {s}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r) (decRx O0 Rc1 s)
     (Hide-hidden csRS' _ Poly.tt
       (Par-sync csRS' ⊤merge (decO O0) (decC Rc1 ⦀ decS s) Poly.tt
         (sVis refl refl)
         (Par-soloL ∅ES ⊤merge (decC Rc1) (decS s) (λ ()) (sVis refl refl)
           (nS-rcvmsg s)))))

-- INNER SYNC: sndack  (decO O2→Og ∥ decS Sa0→Sa1 solo past decC; ∈ csRS').
real-⇒ᵢ-Net (NM.sndack {i} {t} {r} {c}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r) (decRx O2 c Sa0)
     (Hide-hidden csRS' _ Poly.tt
       (Par-sync csRS' ⊤merge (decO O2) (decC c ⦀ decS Sa0) Poly.tt
         (sVis refl refl)
         (Par-soloR ∅ES ⊤merge (decC c) (decS Sa0) (λ ()) (sVis refl refl)
           (nC-sndack c)))))

-- TOP SYNC: ack  (decR R0→R1 solo to decTx-level ∥ decS Sa1→Sag solo to decRx-level; ∈ csTA').
real-⇒ᵢ-Net (NM.ack {i} {t} {o} {c}) =
  Hide-hidden csTA' _ Poly.tt
   (Par-sync csTA' ⊤merge (decTx i t R0) (decRx o c Sa1) Poly.tt
     (Hide-keep csSR' _ (λ ())
       (Par-soloR csSR' ⊤merge (decI i) (decT t ⦀ decR R0) (λ ())
         (Par-soloR ∅ES ⊤merge (decT t) (decR R0) (λ ()) (sVis refl refl)
           (nT-ack t))
         (nI-ack i)))
     (Hide-keep csRS' _ (λ ())
       (Par-soloR csRS' ⊤merge (decO o) (decC c ⦀ decS Sa1) (λ ())
         (Par-soloR ∅ES ⊤merge (decC c) (decS Sa1) (λ ()) (sVis refl refl)
           (nC-ack c))
         (nO-ack o))))

-- INNER SYNC: rcvack  (decI I2→Ig ∥ decR R1→Rg solo past decT; ∈ csSR').
real-⇒ᵢ-Net (NM.rcvack {t} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx I2 t R1) (decRx o c s)
     (Hide-hidden csSR' _ Poly.tt
       (Par-sync csSR' ⊤merge (decI I2) (decT t ⦀ decR R1) Poly.tt
         (sVis refl refl)
         (Par-soloR ∅ES ⊤merge (decT t) (decR R1) (λ ()) (sVis refl refl)
           (nT-rcvack t)))))

-- GUARD gI  (decI Ig→I0, τ; left of Par⊤ csSR', TxSide left at top).
real-⇒ᵢ-Net (NM.gI {t} {r} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx Ig t r) (decRx o c s)
     (Hide-τ csSR' _
       (Par-τ-L csSR' ⊤merge (decI Ig) (decT t ⦀ decR r) (sSil refl))))

-- GUARD gT  (decT Tg→T0, τ; left of ⦀, right of Par⊤ csSR').
real-⇒ᵢ-Net (NM.gT {i} {r} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx i Tg r) (decRx o c s)
     (Hide-τ csSR' _
       (Par-τ-R csSR' ⊤merge (decI i) (decT Tg ⦀ decR r)
         (Par-τ-L ∅ES ⊤merge (decT Tg) (decR r) (sSil refl)))))

-- GUARD gR  (decR Rg→R0, τ; right of ⦀, right of Par⊤ csSR').
real-⇒ᵢ-Net (NM.gR {i} {t} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx i t Rg) (decRx o c s)
     (Hide-τ csSR' _
       (Par-τ-R csSR' ⊤merge (decI i) (decT t ⦀ decR Rg)
         (Par-τ-R ∅ES ⊤merge (decT t) (decR Rg) (sSil refl)))))

-- GUARD gO  (decO Og→O0, τ; left of Par⊤ csRS', RxSide right at top).
real-⇒ᵢ-Net (NM.gO {i} {t} {r} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r) (decRx Og c s)
     (Hide-τ csRS' _
       (Par-τ-L csRS' ⊤merge (decO Og) (decC c ⦀ decS s) (sSil refl))))

-- GUARD gRc  (decC Rcg→Rc0, τ; left of ⦀, right of Par⊤ csRS').
real-⇒ᵢ-Net (NM.gRc {i} {t} {r} {o} {s}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r) (decRx o Rcg s)
     (Hide-τ csRS' _
       (Par-τ-R csRS' ⊤merge (decO o) (decC Rcg ⦀ decS s)
         (Par-τ-L ∅ES ⊤merge (decC Rcg) (decS s) (sSil refl)))))

-- GUARD gSa  (decS Sag→Sa0, τ; right of ⦀, right of Par⊤ csRS').
real-⇒ᵢ-Net (NM.gSa {i} {t} {r} {o} {c}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r) (decRx o c Sag)
     (Hide-τ csRS' _
       (Par-τ-R csRS' ⊤merge (decO o) (decC c ⦀ decS Sag)
         (Par-τ-R ∅ES ⊤merge (decC c) (decS Sag) (sSil refl)))))

------------------------------------------------------------------------
-- D1'.B : the visible converse simulation  cs ⇒ᵥ cs′ → Σ l. ⟦cs⟧N ─[ev l]→ ⟦cs′⟧N.
------------------------------------------------------------------------

real-⇒ᵥ-Net : ∀ {cs cs′} → cs NM.⇒ᵥ cs′
            → Σ[ l ∈ Event√ NetR ] (⟦ cs ⟧N ─[ ev l ]─► ⟦ cs′ ⟧N)

-- VISIBLE input  (decI I0→I1, solo all the way; ∉ csSR', ∉ csTA').
real-⇒ᵥ-Net (NM.input {t} {r} {o} {c} {s}) =
  inputLbl ,
  Hide-keep csTA' _ (λ ())
   (Par-soloL csTA' ⊤merge (decTx I0 t r) (decRx o c s) (λ ())
     (Hide-keep csSR' _ (λ ())
       (Par-soloL csSR' ⊤merge (decI I0) (decT t ⦀ decR r) (λ ())
         (sVis refl refl)
         (nTR-input t r)))
     (nRx-input o c s))

-- VISIBLE output  (decO O1→O2, solo all the way; ∉ csRS', ∉ csTA').
real-⇒ᵥ-Net (NM.output {i} {t} {r} {c} {s}) =
  outputLbl ,
  Hide-keep csTA' _ (λ ())
   (Par-soloR csTA' ⊤merge (decTx i t r) (decRx O1 c s) (λ ())
     (Hide-keep csRS' _ (λ ())
       (Par-soloL csRS' ⊤merge (decO O1) (decC c ⦀ decS s) (λ ())
         (sVis refl refl)
         (nCS-output c s)))
     (nTx-output i t r))

------------------------------------------------------------------------
-- E1: EXPANSION SCAFFOLDING  CopySpec ⪰ Network  (parametrized builder).
--
-- We prove `Network ≈DR CopySpec` via the EXPANSION preorder
-- (`Semantics.Expansion`): building `CopySpec ⪰ ⟦ cs ⟧N` at every
-- reachable abstract state `cs` and feeding it to `⪯→≈DR` (E3) yields
-- `⟦ cs ⟧N ≈DR CopySpec`, hence at `cs0` `Network ≈DR CopySpec`.
--
-- THE SHAPE OF THE PROOF.  The CopySpec lifecycle has THREE states,
--   C0 ─input─► C1 ─output─► Cg ─τ─► C0,
-- whereas the Network side has 192 reachable control-states (the
-- intrinsic diamond product of the six leaf-guards draining
-- asynchronously).  Of those, 112 are PHASE-A (weakly offer input, not
-- output) and 80 are PHASE-B (weakly offer output, not input); phase is
-- well-defined (no state weakly offers both, none offers neither).
--
-- We therefore relate a CopySpec state to a Network state by a tag
-- `CSt ∈ {sC0, sC1, sCg}` whose phase is `sC0,sCg ↦ pA`, `sC1 ↦ pB`:
--   · sC0  ⟷ a phase-A network state             (C0 expands it)
--   · sC1  ⟷ a phase-B network state             (C1 expands it)
--   · sCg  ⟷ the *output-target* phase-A state    (Cg expands it; the
--             extra Cg─τ─►C0 is CopySpec's own move, matched by the
--             network STAYING — fwd; on the network's first τ, Cg fires
--             its single τ to C0 and we drop to sC0 — bwd inj₁).
--
-- The reachable set with phase is captured by a 4-constructor CLOSURE
-- relation `Reach : CS → Phase → Set` (NOT a 192-state enumeration):
-- `cs0` is pA; internal `⇒ᵢ` preserve phase; visible `input` flips A→B,
-- `output` flips B→A.  This is sound by construction (every tag is a
-- genuine cs0-reachable state with its true phase) and the lifecycle
-- lemmas the builder needs are exactly its constructors.
--
-- The builder fills the parts needing NO construction:
--   · bwd.bon-tau  (network τ): reflect (Hide-τ-elim + sim-modA) to
--       `cs ⇒ᵢ cs′`; CopySpec STUTTERS (inj₂), phase preserved.  EXCEPT
--       at sCg, where Cg fires its single τ to C0 (inj₁), dropping to sC0.
--   · fwd.on-tau   (CopySpec τ): C0/C1 are τ-stable ⇒ vacuous; Cg's only
--       τ (Cg→C0) is matched by the network STAYING (τ*-refl).
--   · div→/div←    : both sides are divergence-free ⇒ vacuous.
-- and takes the VISIBLE obligations (E2 + phase soundness) as the
-- parameter record `VisWit` below — proved in E2, NOT here.
------------------------------------------------------------------------

open import Relation.Nullary using (¬_)

-- Phases.
data Phase : Set where pA pB : Phase

-- The reachable-with-phase closure relation (4 constructors).
data Reach : CS → Phase → Set where
  reach-cs0 : Reach cs0 pA
  reach-i   : ∀ {cs cs′ ph} → Reach cs ph → cs ⇒ᵢ cs′ → Reach cs′ ph
  reach-vA  : ∀ {cs cs′}    → Reach cs pA → cs ⇒ᵥ cs′ → Reach cs′ pB
  reach-vB  : ∀ {cs cs′}    → Reach cs pB → cs ⇒ᵥ cs′ → Reach cs′ pA

-- LIFECYCLE LEMMAS (exactly the constructors; named for the report/E3).
reach-init : Reach cs0 pA
reach-init = reach-cs0

reach-internal : ∀ {cs cs′ ph} → Reach cs ph → cs ⇒ᵢ cs′ → Reach cs′ ph
reach-internal = reach-i

reach-input  : ∀ {cs cs′} → Reach cs pA → cs ⇒ᵥ cs′ → Reach cs′ pB
reach-input = reach-vA

reach-output : ∀ {cs cs′} → Reach cs pB → cs ⇒ᵥ cs′ → Reach cs′ pA
reach-output = reach-vB

-- The non-divergence of every decoded network state (reusing MILESTONE 2):
-- `goodU-cs` gives `GoodU ⟦ cs ⟧`, and `GoodU→noDiv` hides it.
¬Div-⟦⟧N : ∀ cs → ¬ Diverges ⟦ cs ⟧N
¬Div-⟦⟧N cs = GoodU→noDiv (goodU-cs cs)

------------------------------------------------------------------------
-- E2: THE STRUCTURAL REACHABILITY INVARIANT (a place-invariant).
--
-- The 192 reachable control-states are EXACTLY characterised by a single
-- ℕ place-invariant plus a structural phase function:
--
--   Inv cs :   #{tr=T1} + #{ra=R1} + #{out∈{O1,O2}} + #{rc=Rc1} + #{sa=Sa1}
--            ≡ #{inp=I2}
--
--   phase cs :  #{inp=I1} + #{tr=T1} + #{out=O1} + #{rc=Rc1}
--               (pA ⟺ ≡0 ; pB ⟺ ≡1)
--
-- `Inv` says there is at most one "in-flight" token, accounted by I2; it
-- holds at cs0 and is preserved by every `⇒ᵢ`/`⇒ᵥ` edge.  Together with the
-- phase agreement (`Reach … pA ⇒ phase ≡ 0`), it implies the LIVENESS
-- engine `liveA`/`liveB` (a phase-A non-input-enabled state always has an
-- internal move), the crux of the abstract drains.
------------------------------------------------------------------------

open import Data.Nat using (zero; suc; _+_)
import Data.Nat.Solver as ℕSolver
open ℕSolver.+-*-Solver
  using ()
  renaming (solve to ℕsolve; _:=_ to _:≡_; _:+_ to _:⊕_; con to ℕcon)

-- per-leaf token / phase indicators -----------------------------------
aT : TP → ℕ
aT T1 = 1
aT _  = 0
aR : RP → ℕ
aR R1 = 1
aR _  = 0
aO : OP → ℕ
aO O1 = 1
aO O2 = 1
aO _  = 0
aC : CP → ℕ
aC Rc1 = 1
aC _   = 0
aS : SP → ℕ
aS Sa1 = 1
aS _   = 0
aI : IP → ℕ
aI I2 = 1
aI _  = 0

-- token count on a state (LHS of the place-invariant).
tok : CS → ℕ
tok cs = aT (tr cs) + aR (ra cs) + aO (out cs) + aC (rc cs) + aS (sa cs)

-- the place-invariant.
Inv : CS → Set
Inv cs = tok cs ≡ aI (inp cs)

-- structural phase.
pI : IP → ℕ
pI I1 = 1
pI _  = 0
pT : TP → ℕ
pT T1 = 1
pT _  = 0
pO : OP → ℕ
pO O1 = 1
pO _  = 0
pC : CP → ℕ
pC Rc1 = 1
pC _   = 0

phaseN : CS → ℕ
phaseN cs = pI (inp cs) + pT (tr cs) + pO (out cs) + pC (rc cs)

------------------------------------------------------------------------
-- E2.a  Inv holds at cs0 and is preserved by every abstract edge.
------------------------------------------------------------------------

Inv-cs0 : Inv cs0
Inv-cs0 = refl

-- `suc`-injectivity (for the rcvack cancellation).
sucinj : ∀ {m n} → suc m ≡ suc n → m ≡ n
sucinj refl = refl

Inv-step : ∀ {cs cs′} → cs ⇒ᵢ cs′ → Inv cs → Inv cs′
-- sndmsg I1T0→I2T1 : tok 0+rest → 1+rest, aI 0→1.  inv: rest≡0 ⇒ suc rest≡1.
Inv-step NM.sndmsg inv = cong suc inv
-- tx T1Rc0→TgRc1 : tok unchanged (1+r+o+0+s = 0+r+o+1+s), aI unchanged.
Inv-step (NM.tx {i} {r} {o} {s}) inv =
  trans (ℕsolve 3 (λ b d e → ℕcon 0 :⊕ b :⊕ d :⊕ ℕcon 1 :⊕ e
                          :≡ ℕcon 1 :⊕ b :⊕ d :⊕ ℕcon 0 :⊕ e)
           refl (aR r) (aO o) (aS s)) inv
-- rcvmsg O0Rc1→O1Rcg : tok unchanged (t+r+0+1+s = t+r+1+0+s).
Inv-step (NM.rcvmsg {i} {t} {r} {s}) inv =
  trans (ℕsolve 3 (λ a b e → a :⊕ b :⊕ ℕcon 1 :⊕ ℕcon 0 :⊕ e
                          :≡ a :⊕ b :⊕ ℕcon 0 :⊕ ℕcon 1 :⊕ e)
           refl (aT t) (aR r) (aS s)) inv
-- sndack O2Sa0→OgSa1 : tok unchanged (t+r+0+c+1 = t+r+1+c+0).
Inv-step (NM.sndack {i} {t} {r} {c}) inv =
  trans (ℕsolve 3 (λ a b d → a :⊕ b :⊕ ℕcon 0 :⊕ d :⊕ ℕcon 1
                          :≡ a :⊕ b :⊕ ℕcon 1 :⊕ d :⊕ ℕcon 0)
           refl (aT t) (aR r) (aC c)) inv
-- ack R0Sa1→R1Sag : tok unchanged (t+1+o+c+0 = t+0+o+c+1).
Inv-step (NM.ack {i} {t} {o} {c}) inv =
  trans (ℕsolve 3 (λ a d e → a :⊕ ℕcon 1 :⊕ d :⊕ e :⊕ ℕcon 0
                          :≡ a :⊕ ℕcon 0 :⊕ d :⊕ e :⊕ ℕcon 1)
           refl (aT t) (aO o) (aC c)) inv
-- rcvack I2R1→IgRg : tok (t+1+o+c+s) → (t+0+o+c+s), aI 1→0.  cancel suc.
Inv-step (NM.rcvack {t} {o} {c} {s}) inv =
  sucinj
    (trans (ℕsolve 4 (λ a d e f → ℕcon 1 :⊕ (a :⊕ ℕcon 0 :⊕ d :⊕ e :⊕ f)
                              :≡ a :⊕ ℕcon 1 :⊕ d :⊕ e :⊕ f)
             refl (aT t) (aO o) (aC c) (aS s))
       inv)
Inv-step NM.gI     inv = inv
Inv-step NM.gT     inv = inv
Inv-step NM.gR     inv = inv
Inv-step NM.gO     inv = inv
Inv-step NM.gRc    inv = inv
Inv-step NM.gSa    inv = inv

Inv-vis : ∀ {cs cs′} → cs ⇒ᵥ cs′ → Inv cs → Inv cs′
Inv-vis NM.input  inv = inv
Inv-vis NM.output inv = inv

------------------------------------------------------------------------
-- E2.b  Phase agreement: Reach … pA ⇒ phaseN ≡ 0 ; Reach … pB ⇒ ≡ 1.
------------------------------------------------------------------------

phase-step : ∀ {cs cs′} → cs ⇒ᵢ cs′ → phaseN cs ≡ phaseN cs′
-- sndmsg I1T0→I2T1 : pI 1→0, pT 0→1.  (1+0+o+c = 0+1+o+c)
phase-step (NM.sndmsg {r} {o} {c} {s}) =
  ℕsolve 2 (λ d e → ℕcon 1 :⊕ ℕcon 0 :⊕ d :⊕ e
                 :≡ ℕcon 0 :⊕ ℕcon 1 :⊕ d :⊕ e)
    refl (pO o) (pC c)
-- tx T1Rc0→TgRc1 : pT 1→0, pC 0→1.
phase-step (NM.tx {i} {r} {o} {s}) =
  ℕsolve 2 (λ a d → a :⊕ ℕcon 1 :⊕ d :⊕ ℕcon 0
                 :≡ a :⊕ ℕcon 0 :⊕ d :⊕ ℕcon 1)
    refl (pI i) (pO o)
-- rcvmsg O0Rc1→O1Rcg : pO 0→1, pC 1→0.
phase-step (NM.rcvmsg {i} {t} {r} {s}) =
  ℕsolve 2 (λ a b → a :⊕ b :⊕ ℕcon 0 :⊕ ℕcon 1
                 :≡ a :⊕ b :⊕ ℕcon 1 :⊕ ℕcon 0)
    refl (pI i) (pT t)
phase-step NM.sndack = refl
phase-step NM.ack    = refl
phase-step NM.rcvack = refl
phase-step NM.gI     = refl
phase-step NM.gT     = refl
phase-step NM.gR     = refl
phase-step NM.gO     = refl
phase-step NM.gRc    = refl
phase-step NM.gSa    = refl

o≢0 : ∀ {n} → suc n ≡ 0 → ⊥
o≢0 ()

-- An out=O1 state (pO=1) has positive phaseN.
phaseN-O1 : ∀ i t c → pI i + pT t + pO O1 + pC c ≡ 0 → ⊥
phaseN-O1 i t c e =
  o≢0 (trans (ℕsolve 3 (λ a b d → ℕcon 1 :⊕ (a :⊕ b :⊕ d)
                              :≡ a :⊕ b :⊕ ℕcon 1 :⊕ d)
                refl (pI i) (pT t) (pC c)) e)

-- From `Inv` with inp=I0 (so tok ≡ 0) the phase is 0.  We case-split on the
-- three phase-relevant leaves; the `token` positions (T1/O1/O2/Rc1) make
-- `tok` (= `Inv`'s LHS) a `suc _`, contradicting `tok ≡ aI I0 = 0`.
Inv-I0-phase0 : ∀ {cs} → inp cs ≡ I0 → Inv cs → phaseN cs ≡ 0
Inv-I0-phase0 {mkCS I0 T0  r O0 Rc0 s} refl inv = refl
Inv-I0-phase0 {mkCS I0 T0  r O0 Rcg s} refl inv = refl
Inv-I0-phase0 {mkCS I0 T0  r Og Rc0 s} refl inv = refl
Inv-I0-phase0 {mkCS I0 T0  r Og Rcg s} refl inv = refl
Inv-I0-phase0 {mkCS I0 Tg  r O0 Rc0 s} refl inv = refl
Inv-I0-phase0 {mkCS I0 Tg  r O0 Rcg s} refl inv = refl
Inv-I0-phase0 {mkCS I0 Tg  r Og Rc0 s} refl inv = refl
Inv-I0-phase0 {mkCS I0 Tg  r Og Rcg s} refl inv = refl
-- token leaves ⇒ tok = suc _ ≡ 0 absurd:
Inv-I0-phase0 {mkCS I0 T1  r o   c   s} refl inv =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ b d e f → ℕcon 1 :⊕ (b :⊕ d :⊕ e :⊕ f)
                                         :≡ ℕcon 1 :⊕ b :⊕ d :⊕ e :⊕ f)
                       refl (aR r) (aO o) (aC c) (aS s)) inv))
Inv-I0-phase0 {mkCS I0 t   r O1  c   s} refl inv =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ a b e f → ℕcon 1 :⊕ (a :⊕ b :⊕ e :⊕ f)
                                         :≡ a :⊕ b :⊕ ℕcon 1 :⊕ e :⊕ f)
                       refl (aT t) (aR r) (aC c) (aS s)) inv))
Inv-I0-phase0 {mkCS I0 t   r O2  c   s} refl inv =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ a b e f → ℕcon 1 :⊕ (a :⊕ b :⊕ e :⊕ f)
                                         :≡ a :⊕ b :⊕ ℕcon 1 :⊕ e :⊕ f)
                       refl (aT t) (aR r) (aC c) (aS s)) inv))
Inv-I0-phase0 {mkCS I0 t   r o   Rc1 s} refl inv =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ a b d f → ℕcon 1 :⊕ (a :⊕ b :⊕ d :⊕ f)
                                         :≡ a :⊕ b :⊕ d :⊕ ℕcon 1 :⊕ f)
                       refl (aT t) (aR r) (aO o) (aS s)) inv))

-- Same for inp = Ig (aI Ig = pI Ig = 0).
Inv-Ig-phase0 : ∀ {cs} → inp cs ≡ Ig → Inv cs → phaseN cs ≡ 0
Inv-Ig-phase0 {mkCS Ig T0  r O0 Rc0 s} refl inv = refl
Inv-Ig-phase0 {mkCS Ig T0  r O0 Rcg s} refl inv = refl
Inv-Ig-phase0 {mkCS Ig T0  r Og Rc0 s} refl inv = refl
Inv-Ig-phase0 {mkCS Ig T0  r Og Rcg s} refl inv = refl
Inv-Ig-phase0 {mkCS Ig Tg  r O0 Rc0 s} refl inv = refl
Inv-Ig-phase0 {mkCS Ig Tg  r O0 Rcg s} refl inv = refl
Inv-Ig-phase0 {mkCS Ig Tg  r Og Rc0 s} refl inv = refl
Inv-Ig-phase0 {mkCS Ig Tg  r Og Rcg s} refl inv = refl
Inv-Ig-phase0 {mkCS Ig T1  r o   c   s} refl inv =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ b d e f → ℕcon 1 :⊕ (b :⊕ d :⊕ e :⊕ f)
                                         :≡ ℕcon 1 :⊕ b :⊕ d :⊕ e :⊕ f)
                       refl (aR r) (aO o) (aC c) (aS s)) inv))
Inv-Ig-phase0 {mkCS Ig t   r O1  c   s} refl inv =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ a b e f → ℕcon 1 :⊕ (a :⊕ b :⊕ e :⊕ f)
                                         :≡ a :⊕ b :⊕ ℕcon 1 :⊕ e :⊕ f)
                       refl (aT t) (aR r) (aC c) (aS s)) inv))
Inv-Ig-phase0 {mkCS Ig t   r O2  c   s} refl inv =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ a b e f → ℕcon 1 :⊕ (a :⊕ b :⊕ e :⊕ f)
                                         :≡ a :⊕ b :⊕ ℕcon 1 :⊕ e :⊕ f)
                       refl (aT t) (aR r) (aC c) (aS s)) inv))
Inv-Ig-phase0 {mkCS Ig t   r o   Rc1 s} refl inv =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ a b d f → ℕcon 1 :⊕ (a :⊕ b :⊕ d :⊕ f)
                                         :≡ a :⊕ b :⊕ d :⊕ ℕcon 1 :⊕ f)
                       refl (aT t) (aR r) (aO o) (aS s)) inv))

phase-input  : ∀ {cs cs′} → cs ⇒ᵥ cs′ → phaseN cs ≡ 0 → phaseN cs′ ≡ 1
-- input I0→I1 : pI 0→1.  goal 1+rest ≡ 1 from rest ≡ 0.
phase-input NM.input  eq = cong suc eq
-- output O1→O2 : the source has out=O1 so phaseN ≡ 0 is impossible.
phase-input (NM.output {i} {t} {r} {c} {s}) eq = ⊥-elim (phaseN-O1 i t c eq)

-- `phase-output` is only ever applied to the OUTPUT edge from a genuine pB
-- state; the `input` edge needs inp=I0, which `Inv` + pB (phaseN≡1) refutes.
phase-output : ∀ {cs cs′} → Inv cs → cs ⇒ᵥ cs′ → phaseN cs ≡ 1 → phaseN cs′ ≡ 0
-- input I0→I1 : a pB state with inp=I0 contradicts `Inv` (gives phaseN≡0≠1).
phase-output {cs} inv NM.input  eq =
  ⊥-elim (o≢0 (trans (sym eq) (Inv-I0-phase0 {cs} refl inv)))
-- output O1→O2 : pO 1→0.  goal rest ≡ 0 from 1+rest ≡ 1.
phase-output {mkCS i t r O1 c s} inv NM.output eq = sucinj (trans (helper i t c) eq)
  where
  -- 1 + phaseN(i t r O2 c s) ≡ phaseN(i t r O1 c s)
  helper : ∀ i t c → suc (pI i + pT t + pO O2 + pC c)
                   ≡ pI i + pT t + pO O1 + pC c
  helper i t c =
    ℕsolve 3 (λ a b d → ℕcon 1 :⊕ (a :⊕ b :⊕ ℕcon 0 :⊕ d)
                     :≡ a :⊕ b :⊕ ℕcon 1 :⊕ d)
      refl (pI i) (pT t) (pC c)

-- Reach gives both Inv and the matching phase number.
reach-Inv : ∀ {cs ph} → Reach cs ph → Inv cs
reach-Inv reach-cs0          = Inv-cs0
reach-Inv (reach-i r step)   = Inv-step step (reach-Inv r)
reach-Inv (reach-vA r step)  = Inv-vis step (reach-Inv r)
reach-Inv (reach-vB r step)  = Inv-vis step (reach-Inv r)

reach-phaseA : ∀ {cs} → Reach cs pA → phaseN cs ≡ 0
reach-phaseB : ∀ {cs} → Reach cs pB → phaseN cs ≡ 1

reach-phaseA reach-cs0         = refl
reach-phaseA (reach-i r step)  =
  trans (sym (phase-step step)) (reach-phaseA r)
reach-phaseA (reach-vB r step) =
  phase-output (reach-Inv r) step (reach-phaseB r)

reach-phaseB (reach-i r step)  =
  trans (sym (phase-step step)) (reach-phaseB r)
reach-phaseB (reach-vA r step) = phase-input step (reach-phaseA r)

------------------------------------------------------------------------
-- E2.c  LIVENESS: a phase-A non-input-enabled state, and a phase-B
-- non-output-enabled state, always have an internal `⇒ᵢ` move.  This is
-- the crux of the abstract drains; it is a finite case analysis on the
-- six leaves, with the unreachable leaf combinations refuted by `Inv`
-- (the place count is wrong) or by the structural phase (a `token` leaf
-- T1/O1/Rc1 contradicts phaseN ≡ 0).
------------------------------------------------------------------------

-- phase-A liveness (inp ≠ I0 ⇒ an internal move).
liveA : ∀ cs → Inv cs → phaseN cs ≡ 0 → inp cs ≢ I0
      → Σ[ cs′ ∈ CS ] (cs ⇒ᵢ cs′)
-- inp = I0 : excluded by hypothesis.
liveA (mkCS I0 t r o c s) inv ph i≢ = ⊥-elim (i≢ refl)
-- inp = I1 : pI I1 = 1, so phaseN = suc _ ≢ 0.
liveA (mkCS I1 t r o c s) inv ph i≢ = ⊥-elim (o≢0 ph)
-- inp = Ig : guard gI.
liveA (mkCS Ig t r o c s) inv ph i≢ = mkCS I0 t r o c s , NM.gI
-- inp = I2 : the in-flight token is somewhere; drive it.
liveA (mkCS I2 t  Rg o c s) inv ph i≢ = mkCS I2 t R0 o c s , NM.gR
liveA (mkCS I2 t  R1 o c s) inv ph i≢ = mkCS Ig t Rg o c s , NM.rcvack
-- ra = R0 from here.
liveA (mkCS I2 Tg R0 o c s) inv ph i≢ = mkCS I2 T0 R0 o c s , NM.gT
-- tr = T1 contradicts phaseN ≡ 0 (pT T1 = 1).
liveA (mkCS I2 T1 R0 o c s) inv ph i≢ = ⊥-elim (o≢0 ph)
-- tr = T0, ra = R0 from here.
liveA (mkCS I2 T0 R0 Og  c   s)   inv ph i≢ = mkCS I2 T0 R0 O0 c s , NM.gO
liveA (mkCS I2 T0 R0 O2  c   Sa0) inv ph i≢ = mkCS I2 T0 R0 Og c Sa1 , NM.sndack
liveA (mkCS I2 T0 R0 O2  c   Sag) inv ph i≢ = mkCS I2 T0 R0 O2 c Sa0 , NM.gSa
-- O2 with Sa1 : tok = aO O2 + aC c + aS Sa1 ≥ 2 ≢ 1 = aI I2.
liveA (mkCS I2 T0 R0 O2  Rc0 Sa1) inv ph i≢ = ⊥-elim (o≢0 (sucinj inv))
liveA (mkCS I2 T0 R0 O2  Rc1 Sa1) inv ph i≢ = ⊥-elim (o≢0 (sucinj inv))
liveA (mkCS I2 T0 R0 O2  Rcg Sa1) inv ph i≢ = ⊥-elim (o≢0 (sucinj inv))
-- out = O1 contradicts phaseN ≡ 0 (pO O1 = 1).
liveA (mkCS I2 T0 R0 O1  c   s)   inv ph i≢ = ⊥-elim (o≢0 ph)
-- out = O0, tr = T0, ra = R0.
liveA (mkCS I2 T0 R0 O0  Rcg s)   inv ph i≢ = mkCS I2 T0 R0 O0 Rc0 s , NM.gRc
-- rc = Rc1 contradicts phaseN ≡ 0 (pC Rc1 = 1).
liveA (mkCS I2 T0 R0 O0  Rc1 s)   inv ph i≢ = ⊥-elim (o≢0 ph)
-- rc = Rc0 : the token must be the pending ack (sa = Sa1).
liveA (mkCS I2 T0 R0 O0  Rc0 Sa1) inv ph i≢ = mkCS I2 T0 R1 O0 Rc0 Sag , NM.ack
-- everything clear ⇒ tok = 0 ≢ 1 = aI I2.
liveA (mkCS I2 T0 R0 O0  Rc0 Sa0) inv ph i≢ = ⊥-elim (o≢0 (sym inv))
liveA (mkCS I2 T0 R0 O0  Rc0 Sag) inv ph i≢ = ⊥-elim (o≢0 (sym inv))

-- phase-B liveness (out ≠ O1 ⇒ an internal move).
liveB : ∀ cs → Inv cs → phaseN cs ≡ 1 → out cs ≢ O1
      → Σ[ cs′ ∈ CS ] (cs ⇒ᵢ cs′)
-- inp = I0 / Ig : `Inv` forces phaseN ≡ 0 ≢ 1.
liveB (mkCS I0 t r o c s) inv ph o≢ =
  ⊥-elim (o≢0 (sym (trans (sym (Inv-I0-phase0 {mkCS I0 t r o c s} refl inv)) ph)))
liveB (mkCS Ig t r o c s) inv ph o≢ =
  ⊥-elim (o≢0 (sym (trans (sym (Inv-Ig-phase0 {mkCS Ig t r o c s} refl inv)) ph)))
-- inp = I1 : drive the transmitter (sndmsg if T0, else guard / refute T1).
liveB (mkCS I1 T0 r o c s) inv ph o≢ = mkCS I2 T1 r o c s , NM.sndmsg
liveB (mkCS I1 Tg r o c s) inv ph o≢ = mkCS I1 T0 r o c s , NM.gT
-- tr = T1 makes phaseN = pI I1 + pT T1 + … = 2 ≢ 1.
liveB (mkCS I1 T1 r o c s) inv ph o≢ = ⊥-elim (o≢0 (sucinj ph))
-- inp = I2 : drive the in-flight token towards the receiver.
liveB (mkCS I2 t  Rg o   c   s)   inv ph o≢ = mkCS I2 t R0 o c s , NM.gR
liveB (mkCS I2 t  R1 o   c   s)   inv ph o≢ = mkCS Ig t Rg o c s , NM.rcvack
-- ra = R0 from here.
liveB (mkCS I2 Tg R0 o   c   s)   inv ph o≢ = mkCS I2 T0 R0 o c s , NM.gT
-- tr ∈ {T0,T1}.
liveB (mkCS I2 t  R0 Og  c   s)   inv ph o≢ = mkCS I2 t R0 O0 c s , NM.gO
-- out = O1 excluded by hypothesis.
liveB (mkCS I2 t  R0 O1  c   s)   inv ph o≢ = ⊥-elim (o≢ refl)
-- out ∈ {O0,O2}.
liveB (mkCS I2 t  R0 o   Rcg s)   inv ph o≢ = mkCS I2 t R0 o Rc0 s , NM.gRc
-- rc ∈ {Rc0,Rc1}.
liveB (mkCS I2 t  R0 o   c   Sag) inv ph o≢ = mkCS I2 t R0 o c Sa0 , NM.gSa
-- sa ∈ {Sa0,Sa1} — now only the two sync states survive `Inv`.
liveB (mkCS I2 T0 R0 O0  Rc1 Sa0) inv ph o≢ = mkCS I2 T0 R0 O1 Rcg Sa0 , NM.rcvmsg
liveB (mkCS I2 T1 R0 O0  Rc0 Sa0) inv ph o≢ = mkCS I2 Tg R0 O0 Rc1 Sa0 , NM.tx
-- the remaining (t,o,c,s) combinations are excluded by `Inv` (wrong token
-- count, refuted by `inv`) or by the phase (phaseN ≡ 0 ≠ 1, refuted by `ph`).
liveB (mkCS I2 T0 R0 O0  Rc0 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sym inv))     -- tok 0
liveB (mkCS I2 T0 R0 O0  Rc0 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sym ph))      -- phase 0
liveB (mkCS I2 T0 R0 O0  Rc1 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 2
liveB (mkCS I2 T0 R0 O2  Rc0 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sym ph))      -- phase 0
liveB (mkCS I2 T0 R0 O2  Rc0 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 2
liveB (mkCS I2 T0 R0 O2  Rc1 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 2
liveB (mkCS I2 T0 R0 O2  Rc1 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 3
liveB (mkCS I2 T1 R0 O0  Rc0 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 2
liveB (mkCS I2 T1 R0 O0  Rc1 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 2
liveB (mkCS I2 T1 R0 O0  Rc1 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 3
liveB (mkCS I2 T1 R0 O2  Rc0 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 2
liveB (mkCS I2 T1 R0 O2  Rc0 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 3
liveB (mkCS I2 T1 R0 O2  Rc1 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 3
liveB (mkCS I2 T1 R0 O2  Rc1 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))  -- tok 4

------------------------------------------------------------------------
-- E2.d  THE ABSTRACT DRAINS (pure NetModel, by well-founded recursion on μ).
--
--   drainA : a phase-A reachable state internally reduces to an
--            input-enabled state (inp ≡ I0);
--   drainB : a phase-B reachable state internally reduces to an
--            output-enabled state (out ≡ O1).
--
-- `_⇒ᵢ*_` is the reflexive-transitive closure of `_⇒ᵢ_`.  Each step strictly
-- drops `μ` (`μ-dec`), so the recursion is well-founded; `liveA`/`liveB`
-- supply the move while not yet enabled.
------------------------------------------------------------------------

infix 4 _⇒ᵢ*_
data _⇒ᵢ*_ : CS → CS → Set where
  ε   : ∀ {cs} → cs ⇒ᵢ* cs
  _◅_ : ∀ {cs cs′ cs″} → cs ⇒ᵢ cs′ → cs′ ⇒ᵢ* cs″ → cs ⇒ᵢ* cs″

-- decide `inp ≡ I0`.
decI0 : ∀ i → (i ≡ I0) ⊎ (i ≢ I0)
decI0 I0 = inj₁ refl
decI0 I1 = inj₂ (λ ())
decI0 I2 = inj₂ (λ ())
decI0 Ig = inj₂ (λ ())
decO1 : ∀ o → (o ≡ O1) ⊎ (o ≢ O1)
decO1 O0 = inj₂ (λ ())
decO1 O1 = inj₁ refl
decO1 O2 = inj₂ (λ ())
decO1 Og = inj₂ (λ ())

drainA-acc : ∀ cs → Reach cs pA → Acc _<_ (NM.μ cs)
           → Σ[ cs-d ∈ CS ] ((cs ⇒ᵢ* cs-d) × (inp cs-d ≡ I0))
drainA-acc cs r (acc rs) with decI0 (inp cs)
... | inj₁ i≡    = cs , ε , i≡
... | inj₂ i≢ with liveA cs (reach-Inv r) (reach-phaseA r) i≢
...   | cs′ , step with drainA-acc cs′ (reach-i r step) (rs (NM.μ-dec step))
...     | cs-d , path , i≡ = cs-d , step ◅ path , i≡

drainA : ∀ cs → Reach cs pA
       → Σ[ cs-d ∈ CS ] ((cs ⇒ᵢ* cs-d) × (inp cs-d ≡ I0))
drainA cs r = drainA-acc cs r (<-wellFounded (NM.μ cs))

drainB-acc : ∀ cs → Reach cs pB → Acc _<_ (NM.μ cs)
           → Σ[ cs-d ∈ CS ] ((cs ⇒ᵢ* cs-d) × (out cs-d ≡ O1))
drainB-acc cs r (acc rs) with decO1 (out cs)
... | inj₁ o≡    = cs , ε , o≡
... | inj₂ o≢ with liveB cs (reach-Inv r) (reach-phaseB r) o≢
...   | cs′ , step with drainB-acc cs′ (reach-i r step) (rs (NM.μ-dec step))
...     | cs-d , path , o≡ = cs-d , step ◅ path , o≡

drainB : ∀ cs → Reach cs pB
       → Σ[ cs-d ∈ CS ] ((cs ⇒ᵢ* cs-d) × (out cs-d ≡ O1))
drainB cs r = drainB-acc cs r (<-wellFounded (NM.μ cs))

------------------------------------------------------------------------
-- E2.e  Realise an abstract drain as a Network τ* run.
------------------------------------------------------------------------

real-⇒ᵢ*-Net : ∀ {cs cs-d} → cs ⇒ᵢ* cs-d → ⟦ cs ⟧N ─[τ*]─► ⟦ cs-d ⟧N
real-⇒ᵢ*-Net ε            = τ*-refl
real-⇒ᵢ*-Net (step ◅ path) =
  τ*-step (real-⇒ᵢ-Net step) (real-⇒ᵢ*-Net path)

------------------------------------------------------------------------
-- The VISIBLE obligations (E2 + phase soundness) — PARAMETERS only.
-- Everything visible-and-phase-sensitive the builder cannot derive from
-- the divergence/τ machinery is collected here; E2 proves it (NOT here).
--   `_≢I0_` / `_≢O1_` are the structural facts that an output-target
--   phase-A state has no strong visible step (input needs I0, output O1).
------------------------------------------------------------------------

record VisWit : Set₁ where
  field
    -- FWD (CopySpec's visible step weakly matched by the network):
    --   from a phase-A state the network ═input═► a phase-B state;
    --   from a phase-B state the network ═output═► a phase-A state.  The
    --   output-target additionally has inp≠I0 ∧ out≠O1 (no strong ev),
    --   which lets `expG`'s bon-ev be discharged at Cg.
    fwd-in  : ∀ {cs} → Reach cs pA
            → Σ[ cs′ ∈ CS ] ((⟦ cs ⟧N ═[ ev inputLbl  ]═► ⟦ cs′ ⟧N) × Reach cs′ pB)
    fwd-out : ∀ {cs} → Reach cs pB
            → Σ[ cs′ ∈ CS ]
                ((⟦ cs ⟧N ═[ ev outputLbl ]═► ⟦ cs′ ⟧N)
                 × Reach cs′ pA × (inp cs′ ≢ I0) × (out cs′ ≢ O1))
    -- BWD (the network's strong visible step, label-resolved + Reach-tracked):
    --   at phase-A the only strong visible label is `input`, landing at pB;
    --   at phase-B the only strong visible label is `output`, landing at pA.
    bwd-in  : ∀ {cs} {l : Event√ NetR} {t₂′} → Reach cs pA
            → ⟦ cs ⟧N ─[ ev l ]─► t₂′
            → Σ[ eq ∈ l ≡ inputLbl ] (Σ[ cs′ ∈ CS ] ((t₂′ ≡ ⟦ cs′ ⟧N) × Reach cs′ pB))
    --   the output-target is again an output-target (inp≠I0 ∧ out≠O1).
    bwd-out : ∀ {cs} {l : Event√ NetR} {t₂′} → Reach cs pB
            → ⟦ cs ⟧N ─[ ev l ]─► t₂′
            → Σ[ eq ∈ l ≡ outputLbl ]
                (Σ[ cs′ ∈ CS ]
                  ((t₂′ ≡ ⟦ cs′ ⟧N) × Reach cs′ pA × (inp cs′ ≢ I0) × (out cs′ ≢ O1)))
    -- A phase-A state with inp≠I0 ∧ out≠O1 has NO strong visible step.
    noev-AO : ∀ {cs} {l : Event√ NetR} {t₂′}
            → inp cs ≢ I0 → out cs ≢ O1 → ⟦ cs ⟧N ─[ ev l ]─► t₂′ → ⊥

------------------------------------------------------------------------
-- E2.f  PROVING `theVisWit : VisWit`.
------------------------------------------------------------------------

-- transitivity of `⇒ᵢ*` (used to keep the drain's `Reach` evidence).
reach-i* : ∀ {cs cs-d ph} → Reach cs ph → cs ⇒ᵢ* cs-d → Reach cs-d ph
reach-i* r ε            = r
reach-i* r (step ◅ path) = reach-i* (reach-i r step) path

-- A phase-B state never has inp ≡ I0 (else `Inv` ⇒ phaseN ≡ 0 ≠ 1).
pB-inp≢I0 : ∀ {cs} → Reach cs pB → inp cs ≢ I0
pB-inp≢I0 {cs} r i≡ =
  o≢0 (sym (trans (sym (Inv-I0-phase0 {cs} i≡ (reach-Inv r))) (reach-phaseB r)))

-- A label-aware non-csTA visible inversion.  We expose the WITNESSED leaf
-- shape (input ⇒ source has inp=I0; output ⇒ source has out=O1) so the
-- abstract `⇒ᵥ` constructor is *determined* (no spurious cross cases).
data uVisR (cs : CS) {B} (e : Net ⊤ B) (a : B) (W′ : NetProc) : Set₁ where
  uIn  : ∀ {t r o c s} → cs ≡ mkCS I0 t r o c s
       → evl (evLabel B e a) ≡ inputLbl  → W′ ≡ ⟦ mkCS I1 t r o c s ⟧
       → uVisR cs e a W′
  uOut : ∀ {i t r c s} → cs ≡ mkCS i t r O1 c s
       → evl (evLabel B e a) ≡ outputLbl → W′ ≡ ⟦ mkCS i t r O2 c s ⟧
       → uVisR cs e a W′

sim-uVis-lbl : ∀ cs {B} {e : Net ⊤ B} {a} {W′}
             → ¬ csTA' .mem (B , e) a
             → ⟦ cs ⟧ ─[ ev (evl (evLabel B e a)) ]─► W′
             → uVisR cs e a W′
sim-uVis-lbl (mkCS i t r o c s) ¬cs st
  with Par-ev-elim csTA' ⊤merge (decTx i t r) (decRx o c s) st
... | evL _ Txev with sim-Tx-ev {i} {t} {r} Txev
...   | inj₁ (refl , Lin , Weq) =
        uIn refl Lin (cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s))) Weq)
...   | inj₂ (inj₁ (_ , Ltx  , _)) = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , _ , _ , Lack , _)) = ⊥-elim (¬cs (ackg→mem Lack))
sim-uVis-lbl (mkCS i t r o c s) ¬cs st
  | evR _ Rxev with sim-Rx-ev {o} {c} {s} Rxev
...   | inj₁ (refl , Lout , Weq) =
        uOut refl Lout (cong (λ z → ((decTx i t r) ∥⇘ csTA' ⇙ z)) Weq)
...   | inj₂ (inj₁ (_ , _ , _ , Ltx  , _)) = ⊥-elim (¬cs (txg→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) = ⊥-elim (¬cs (ackLbl→mem Lack))
sim-uVis-lbl (mkCS i t r o c s) ¬cs st | evSync mem _ _ = ⊥-elim (¬cs mem)
sim-uVis-lbl (mkCS i t r o c s) ¬cs st
  | evBoth _ Txev Rxev with sim-Tx-ev {i} {t} {r} Txev | sim-Rx-ev {o} {c} {s} Rxev
...   | inj₁ (_ , Lin , _)        | inj₁ (_ , Lout , _) =
          ⊥-elim (inputLbl≢outputLbl (trans (sym Lin) Lout))
...   | inj₁ (_ , Lin , _)        | inj₂ (inj₁ (_ , _ , _ , Ltx , _)) =
          ⊥-elim (inputLbl≢txg (trans (sym Lin) Ltx))
...   | inj₁ (_ , Lin , _)        | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (inputLbl≢ackLbl (trans (sym Lin) Lack))
...   | inj₂ (inj₁ (_ , Ltx , _)) | _ = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , _ , _ , Lack , _)) | _ = ⊥-elim (¬cs (ackg→mem Lack))

-- Reflect a network strong visible step into the same label-resolved shape.
data netVisR (cs : CS) (l : Event√ NetR) (t₂′ : NetProc) : Set₁ where
  nIn  : ∀ {t r o c s} → cs ≡ mkCS I0 t r o c s
       → l ≡ inputLbl  → t₂′ ≡ ⟦ mkCS I1 t r o c s ⟧N → netVisR cs l t₂′
  nOut : ∀ {i t r c s} → cs ≡ mkCS i t r O1 c s
       → l ≡ outputLbl → t₂′ ≡ ⟦ mkCS i t r O2 c s ⟧N → netVisR cs l t₂′

-- The decoded state never terminates: `force ⟦cs⟧` is always a `react`
-- (the input leaf `decI i` is always a `react` menu), so the `√` branch of
-- `Hide-ev-elim` is impossible.
decI-noret : ∀ i {x} → PTree.force (decI i) ≡ ret x → ⊥
decI-noret I0 ()
decI-noret I1 ()
decI-noret I2 ()
decI-noret Ig ()

decTx-noret : ∀ i t r {x} → PTree.force (decTx i t r) ≡ ret x → ⊥
decTx-noret i t r eqf
  with Par-force-ret-inv csSR' ⊤merge {P = decI i} {Q = decT t ⦀ decR r}
         (fHide-ret-inv csSR' ((decI i) ∥⇘ csSR' ⇙ (decT t ⦀ decR r)) eqf)
... | r₁ , _ , decIret , _ , _ = decI-noret i decIret

⟦⟧-noret : ∀ cs {x} → PTree.force ⟦ cs ⟧ ≡ ret x → ⊥
⟦⟧-noret (mkCS i t r o c s) eqf
  with Par-force-ret-inv csTA' ⊤merge {P = decTx i t r} {Q = decRx o c s} eqf
... | r₁ , _ , decTxret , _ , _ = decTx-noret i t r decTxret

reflectV : ∀ cs {l : Event√ NetR} {t₂′} → ⟦ cs ⟧N ─[ ev l ]─► t₂′
         → netVisR cs l t₂′
reflectV cs step with Hide-ev-elim csTA' ⟦ cs ⟧ step
... | heV T′ ¬cs Tev with sim-uVis-lbl cs ¬cs Tev
...   | uIn  ceq Lin  Weq = nIn  ceq Lin  (cong (_∖ csTA') Weq)
...   | uOut ceq Lout Weq = nOut ceq Lout (cong (_∖ csTA') Weq)
reflectV cs step | he√ eqf = ⊥-elim (⟦⟧-noret cs eqf)

-- A phase-A network state offers NO `output` (out=O1 ⇒ phaseN ≥ 1 ≠ 0).
phaseA-out≢O1 : ∀ {cs} → Reach cs pA → out cs ≢ O1
phaseA-out≢O1 {mkCS i t rr O1 c s} rA oeq = phaseN-O1 i t c (reach-phaseA rA)
phaseA-out≢O1 {mkCS i t rr O0 c s} rA ()
phaseA-out≢O1 {mkCS i t rr O2 c s} rA ()
phaseA-out≢O1 {mkCS i t rr Og c s} rA ()

-- The output-target (out=O2) of an `output` step satisfies inp≠I0 ∧ out≠O1.
out-step-tgt : ∀ {i t r c s} → out (mkCS i t r O2 c s) ≢ O1
out-step-tgt ()

theVisWit : VisWit
theVisWit = record
  { fwd-in  = λ {cs} r →
      let (cs-d , path , i≡) = drainA cs r
          rA               = reach-i* r path
      in fwd-in-build cs r cs-d path i≡ rA
  ; fwd-out = λ {cs} r →
      let (cs-d , path , o≡) = drainB cs r
          rB               = reach-i* r path
      in fwd-out-build cs r cs-d path o≡ rB
  ; bwd-in  = λ {cs} {l} {t₂′} r step → bwd-in-build cs r step
  ; bwd-out = λ {cs} {l} {t₂′} r step → bwd-out-build cs r step
  ; noev-AO = λ {cs} {l} {t₂′} i≢ o≢ step → noev-build cs i≢ o≢ step
  }
  where
  -- fwd-in : drain to inp=I0, then the input is enabled.
  fwd-in-build :
    ∀ cs (r : Reach cs pA) cs-d → cs ⇒ᵢ* cs-d → inp cs-d ≡ I0 → Reach cs-d pA
    → Σ[ cs′ ∈ CS ] ((⟦ cs ⟧N ═[ ev inputLbl ]═► ⟦ cs′ ⟧N) × Reach cs′ pB)
  fwd-in-build cs r (mkCS I0 t rr o c s) path refl rA =
    mkCS I1 t rr o c s ,
    wev (real-⇒ᵢ*-Net path) (proj₂ (real-⇒ᵥ-Net (NM.input {t} {rr} {o} {c} {s})))
        τ*-refl′ ,
    reach-vA rA NM.input
    where
    -- `real-⇒ᵥ-Net NM.input` returns `(inputLbl , step)`; project the step.
    τ*-refl′ : ⟦ mkCS I1 t rr o c s ⟧N ─[τ*]─► ⟦ mkCS I1 t rr o c s ⟧N
    τ*-refl′ = τ*-refl

  -- fwd-out : drain to out=O1, then the output is enabled.
  fwd-out-build :
    ∀ cs (r : Reach cs pB) cs-d → cs ⇒ᵢ* cs-d → out cs-d ≡ O1 → Reach cs-d pB
    → Σ[ cs′ ∈ CS ]
        ((⟦ cs ⟧N ═[ ev outputLbl ]═► ⟦ cs′ ⟧N)
         × Reach cs′ pA × (inp cs′ ≢ I0) × (out cs′ ≢ O1))
  fwd-out-build cs r (mkCS i t rr O1 c s) path refl rB =
    mkCS i t rr O2 c s ,
    wev (real-⇒ᵢ*-Net path) (proj₂ (real-⇒ᵥ-Net (NM.output {i} {t} {rr} {c} {s})))
        τ*-refl ,
    reach-vB rB NM.output ,
    (λ i≡ → pB-inp≢I0 rB i≡) ,
    out-step-tgt {i} {t} {rr} {c} {s}

  -- bwd-in : invert the network ev; at phase A it must be input.
  bwd-in-build :
    ∀ cs {l : Event√ NetR} {t₂′} → Reach cs pA → ⟦ cs ⟧N ─[ ev l ]─► t₂′
    → Σ[ eq ∈ l ≡ inputLbl ] (Σ[ cs′ ∈ CS ] ((t₂′ ≡ ⟦ cs′ ⟧N) × Reach cs′ pB))
  bwd-in-build cs r step with reflectV cs step
  ... | nIn  {t} {rr} {o} {c} {s} refl Lin Weq =
        Lin , mkCS I1 t rr o c s , Weq , reach-vA r NM.input
  -- output at phase A is impossible (phaseA-out≢O1).
  ... | nOut refl Lout Weq = ⊥-elim (phaseA-out≢O1 r refl)

  -- bwd-out : invert the network ev; at phase B it must be output.
  bwd-out-build :
    ∀ cs {l : Event√ NetR} {t₂′} → Reach cs pB → ⟦ cs ⟧N ─[ ev l ]─► t₂′
    → Σ[ eq ∈ l ≡ outputLbl ]
        (Σ[ cs′ ∈ CS ]
          ((t₂′ ≡ ⟦ cs′ ⟧N) × Reach cs′ pA × (inp cs′ ≢ I0) × (out cs′ ≢ O1)))
  bwd-out-build cs r step with reflectV cs step
  ... | nOut {i} {t} {rr} {c} {s} refl Lout Weq =
        Lout , mkCS i t rr O2 c s , Weq , reach-vB r NM.output ,
        (λ i≡ → pB-inp≢I0 r i≡) , out-step-tgt {i} {t} {rr} {c} {s}
  -- input at phase B forces inp=I0, impossible (pB-inp≢I0).
  ... | nIn refl Lin Weq = ⊥-elim (pB-inp≢I0 r refl)

  -- noev-AO : an inp≠I0 ∧ out≠O1 state offers no strong visible event.
  noev-build :
    ∀ cs {l : Event√ NetR} {t₂′} → inp cs ≢ I0 → out cs ≢ O1
    → ⟦ cs ⟧N ─[ ev l ]─► t₂′ → ⊥
  noev-build cs i≢ o≢ step with reflectV cs step
  ... | nIn  refl Lin  Weq = i≢ refl
  ... | nOut refl Lout Weq = o≢ refl

------------------------------------------------------------------------
-- THE GENERIC EXPANSION BUILDER (parametrized by `VisWit`).
--
-- Three mutually-corecursive builders, one per CopySpec tag:
--   expA :  C0 ⪰ ⟦cs⟧N   for a phase-A state cs
--   expB :  C1 ⪰ ⟦cs⟧N   for a phase-B state cs
--   expG :  Cg ⪰ ⟦cs⟧N   for an *output-target* phase-A state
--           (carries inp≠I0 ∧ out≠O1 so its bon-ev is refutable until the
--            network's first τ collapses Cg to C0 and drops us to expA).
--
-- The τ / divergence halves are constructed here (no VisWit needed); the
-- VISIBLE halves consult `w`.
------------------------------------------------------------------------

module _ (w : VisWit) where
  open VisWit w

  expA : ∀ cs → Reach cs pA → C0 ⪰ ⟦ cs ⟧N
  expB : ∀ cs → Reach cs pB → C1 ⪰ ⟦ cs ⟧N
  expG : ∀ cs → inp cs ≢ I0 → out cs ≢ O1 → Reach cs pA → Cg ⪰ ⟦ cs ⟧N

  -- shared: reflect a network τ to an internal `⇒ᵢ` step (phase preserved).
  reflectτ : ∀ cs {t₂′} → ⟦ cs ⟧N ─[ τ ]─► t₂′
           → Σ[ cs′ ∈ CS ] ((cs ⇒ᵢ cs′) × (t₂′ ≡ ⟦ cs′ ⟧N))
  reflectτ cs step with Hide-τ-elim csTA' ⟦ cs ⟧ step
  ... | hτP T′ Tτ refl      = let (cs′ , red , Weq) = sim-modA cs (maτ Tτ)
                              in cs′ , red , cong (_∖ csTA') Weq
  ... | hτH T′ mem Tev refl = let (cs′ , red , Weq) = sim-modA cs (maE mem Tev)
                              in cs′ , red , cong (_∖ csTA') Weq

  -- ===========================  expA  (C0)  ===========================
  -- fwd: C0's input matched WEAKLY by the network (VisWit.fwd-in).
  --   (`sRet` is impossible: C0 = CopySpec is a Par⊤, never a `ret`.)
  expA cs r .Expand.fwd .WSimF.on-ev (sRet ())
  expA cs r .Expand.fwd .WSimF.on-ev (sVis eqf breq) with C0-evL (sVis eqf breq)
  ... | refl , refl with fwd-in r
  ...   | cs′ , wstep , r′ = ⟦ cs′ ⟧N , wstep , expB cs′ r′
  -- C0 is τ-stable ⇒ no τ.
  expA cs r .Expand.fwd .WSimF.on-tau step = ⊥-elim (C0-noτ step)
  -- bwd: a network τ → ⇒ᵢ; C0 STUTTERS (inj₂), phase preserved.
  expA cs r .Expand.bwd .ExpBwdF.bon-tau step with reflectτ cs step
  ... | cs′ , red , refl = inj₂ (expA cs′ (reach-i r red))
  -- bwd: a network strong ev (input, at pA) matched by C0─input─►C1.
  expA cs r .Expand.bwd .ExpBwdF.bon-ev step with bwd-in r step
  ... | refl , cs′ , refl , r′ = C1 , C0─input─►C1 , expB cs′ r′
  expA cs r .Expand.div→ d = ⊥-elim (¬Div-C0 d)
  expA cs r .Expand.div← d = ⊥-elim (¬Div-⟦⟧N cs d)

  -- ===========================  expB  (C1)  ===========================
  expB cs r .Expand.fwd .WSimF.on-ev (sRet ())
  expB cs r .Expand.fwd .WSimF.on-ev (sVis eqf breq) with C1-evL (sVis eqf breq)
  ... | refl , refl with fwd-out r
  ...   | cs′ , wstep , r′ , i≢ , o≢ = ⟦ cs′ ⟧N , wstep , expG cs′ i≢ o≢ r′
  expB cs r .Expand.fwd .WSimF.on-tau step = ⊥-elim (C1-noτ step)
  expB cs r .Expand.bwd .ExpBwdF.bon-tau step with reflectτ cs step
  ... | cs′ , red , refl = inj₂ (expB cs′ (reach-i r red))
  expB cs r .Expand.bwd .ExpBwdF.bon-ev step with bwd-out r step
  ... | refl , cs′ , refl , r′ , i≢ , o≢ = Cg , C1─output─►Cg , expG cs′ i≢ o≢ r′
  expB cs r .Expand.div→ d = ⊥-elim (¬Div-C1 d)
  expB cs r .Expand.div← d = ⊥-elim (¬Div-⟦⟧N cs d)

  -- ===========================  expG  (Cg)  ===========================
  -- fwd: Cg's only move is τ→C0, matched by the network STAYING (τ*-refl).
  expG cs i≢ o≢ r .Expand.fwd .WSimF.on-ev (sRet ())
  expG cs i≢ o≢ r .Expand.fwd .WSimF.on-ev (sVis eqf breq) = ⊥-elim (Cg-noev (sVis eqf breq))
  expG cs i≢ o≢ r .Expand.fwd .WSimF.on-tau step with Cg-τ step
  ... | refl = ⟦ cs ⟧N , wτ τ*-refl , expA cs r
  -- bwd: a network τ → Cg fires its single τ to C0 (inj₁), drop to expA.
  expG cs i≢ o≢ r .Expand.bwd .ExpBwdF.bon-tau step with reflectτ cs step
  ... | cs′ , red , refl = inj₁ (C0 , Cg─τ─►C0 , expA cs′ (reach-i r red))
  -- bwd: the output-target has NO strong ev (inp≠I0 ∧ out≠O1) ⇒ refute.
  expG cs i≢ o≢ r .Expand.bwd .ExpBwdF.bon-ev step = ⊥-elim (noev-AO {cs = cs} i≢ o≢ step)
  expG cs i≢ o≢ r .Expand.div→ d = ⊥-elim (¬Div-Cg d)
  expG cs i≢ o≢ r .Expand.div← d = ⊥-elim (¬Div-⟦⟧N cs d)

------------------------------------------------------------------------
-- E3.  MASTER KEY & COROLLARIES.
--
--   Network ≈DR CopySpec        (the master key: divergence-respecting
--                                weak bisimulation, built by the E1
--                                expansion at `theVisWit`/`cs0`)
--     ⇒ Network ≈FD CopySpec     (failures-divergences equivalence —
--                                FDR's `[FD=` BOTH ways; via drbisim→≈FD,
--                                which internally relies on the certified
--                                postulate `¬-divergent→normal` from
--                                Semantics.DRImpliesFD — APPROVED)
--       ⇒ failures-half both ways  (Network ⊑F⊥ CopySpec, CopySpec ⊑F⊥ Network)
--     ⇒ Network ⟺T CopySpec      (trace equivalence; derived from the
--                                weak-bisim shadow drbisim→wbisim WITHOUT
--                                the postulate).
--
-- Defeq used in step 1:  `C0 = CopySpec` (definitional, see C0's def) and
-- `⟦ cs0 ⟧N ≡ Network` (decN-cs0 = refl, definitional), so the builder's
-- result type `C0 ⪰ ⟦ cs0 ⟧N` is `CopySpec ⪰ Network` on the nose — no
-- `subst` is needed (decN-cs0 reduces to refl).
------------------------------------------------------------------------

-- 1.  The expansion at the start state, with its type reduced via the
--     two definitional equalities (C0 = CopySpec, ⟦ cs0 ⟧N = Network).
net-exp : CopySpec ⪰ Network
net-exp = expA theVisWit cs0 reach-cs0

-- 2.  Master key:  Network ≈DR CopySpec
--     (⪯→≈DR : t₁ ⪰ t₂ → t₂ ≈DR t₁, with t₁ = CopySpec, t₂ = Network).
net≈DR : Network ≈DR CopySpec
net≈DR = ⪯→≈DR net-exp

-- 3.  Failures-divergences equivalence (FDR `[FD=` both ways).
net≈FD : Network ≈FD CopySpec
net≈FD = drbisim→≈FD net≈DR

-- 4.  The headline FAILURES results (both directions of ≈FD).
net⊑FD : Network ⊑FD CopySpec
net⊑FD = proj₁ net≈FD

spec⊑FD : CopySpec ⊑FD Network
spec⊑FD = proj₂ net≈FD

--   The failures-half both ways.  `CopySpec ⊑F⊥ Network` is the standard
--   refinement statement "the Network refines the CopySpec".
net⊑F⊥ : Network ⊑F⊥ CopySpec
net⊑F⊥ = proj₁ net⊑FD

spec⊑F⊥ : CopySpec ⊑F⊥ Network
spec⊑F⊥ = proj₁ spec⊑FD

-- 5.  TRACE equivalence (derivable from ≈DR via its weak-bisim shadow,
--     WITHOUT the ¬-divergent→normal postulate).
net≈W : Wbisim NetR Network CopySpec
net≈W = drbisim→wbisim net≈DR

--   `P ⊑T Q = ∀ s → traces Q s → traces P s`, and
--   `traces-respects-≈ : Wbisim R P Q → (traces P s → traces Q s)
--                                      × (traces Q s → traces P s)`.
net⊑T : Network ⊑T CopySpec
net⊑T s = proj₂ (traces-respects-≈ net≈W)

spec⊑T : CopySpec ⊑T Network
spec⊑T s = proj₁ (traces-respects-≈ net≈W)

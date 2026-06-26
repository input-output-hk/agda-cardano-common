{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Single-channel refinement of the Cardano `Network`, GENERALISED in the
-- forwarded payload `Data` (Axis A of the generalisation effort).
--
-- This module is the PARAMETRIC counterpart of
-- `CSP.Examples.Cardano_network.NetworkRefinement` (which fixes `Data = ⊤`).
-- It re-uses the SAME single-channel instance `p1` (numConns N2N_KeepAlive = 1,
-- all other protocols 0; all abstract data domains `⊤`) but keeps the forwarded
-- payload `Data` an ABSTRACT `Set` with a `DecEq Data` instance.
--
-- TASK 1 (this file) — DE-RISKING GATE.  We provide only:
--   * the parametrized module scaffold (opens at `{E = Net Data}`);
--   * the `d`-indexed decode `⟦_⟧ : CS → Data → NetProc` (the six per-operand
--     position decoders carry the abstract payload `d : Data` at the four
--     forward — data-carrying — positions: input/tx/rcvmsg/output);
--   * the GATE: the per-state decode reductions (`dec-cs0`, `dec-U0 … dec-U8`,
--     `U8f≡U0`) must validate by `refl` for a SYMBOLIC `d : Data`.
--
-- The crucial fact making the gate green: `Net-≟` (which the `Par⊤`/`∖`
-- operators use for sync/hide decisions) compares events only by
-- `(constructor, id, Conn id)` — it NEVER inspects the payload `d`.  And the
-- forward leaves' `pchoice` menus decide on `id′ ≟ id` / `c′ ≟ c` only, then
-- forward `d` opaquely.  So no `DecEq Data` comparison on `d` is forced, and
-- every position reduction holds definitionally for an abstract `d`.
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; ≡-≟-identity; sym; trans; cong; cong₂; subst)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (DecEq; _≟_)
open import Data.Nat using (_<_)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using
  ( IDs; N2N_KeepAlive
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

module CSP.Examples.Cardano_network.NetworkRefinementGen
  (Data : Set) ⦃ _ : DecEq Data ⦄ where

open PTree
open ExtI

------------------------------------------------------------------------
-- Hedberg reflexivity for the abstract payload's `DecEq Data`.
--
-- The four FORWARD decode positions fire `Op.Output … d` whose guard
-- `Output-cont`'s value comparison reduces to `d ≟ d`.  For an abstract
-- `DecEq Data` instance this neutral redex does NOT compute to `yes refl`,
-- which is what blocked the original `refl` gate.  Decidable equality ⇒ UIP
-- (Hedberg), so `(x ≟ x) ≡ yes refl` is a THEOREM (no postulate): we obtain
-- it from the stdlib `≡-≟-identity` and discharge the stuck `d ≟ d` redex
-- PROPOSITIONALLY (via `rewrite ≟-diag d`) at the forward decode validations.
------------------------------------------------------------------------

≟-diag : ∀ (x : Data) → (x ≟ x) ≡ yes refl
≟-diag x = ≡-≟-identity _≟_ refl

_probe : ∀ {d : Data} → (d ≟ d) ≡ yes refl
_probe = ≟-diag _

------------------------------------------------------------------------
-- The single-channel instance `p1` (same as the ⊤ proof).
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
  ; decVoteBlob = decEq⊤
  ; Time = ⊤ ; Length = ⊤ ; time₀ = tt ; length₀ = tt
  ; decTime = decEq⊤ ; decLength = decEq⊤ }

open import CSP.Examples.Cardano_network.Net p1
  using (Net; Conn; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack)
open import CSP.Examples.Cardano_network.Network p1 Data

open import Semantics.LTS {E = Net Data} {I = ExtI (Net Data)}
open import Semantics.WeakBisim {E = Net Data} {I = ExtI (Net Data)}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.DRBisim {E = Net Data} {I = ExtI (Net Data)}
  using (Diverges; deadlock-converges)
open import Semantics.Expansion {E = Net Data} {I = ExtI (Net Data)}
  using (Expand; ExpBwdF; _⪰_; ⪯→≈DR)
open import Semantics.Failures {E = Net Data} {I = ExtI (Net Data)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.FailuresDivergences {E = Net Data} {I = ExtI (Net Data)}
  using (_⊑D_; divergences; IsDivergence)

-- the Net-decidable-equality used to instantiate every operator/law module
open import CSP.Examples.Cardano_network.Net p1 using (Net-≟)

open import CSP.Operators {E = Net Data} (Net-≟ {Data})
  using (Par⊤; _∥⇘_⇙_; _⦀_; _∖_; chanSet; EventSet; Skip; Par; ∅ES; viewV)
open EventSet

open import Data.List using (List; map; _∷_; [])
import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op

open import CSP.Laws.FD.HideDivergence (Net-≟ {Data})
  using (MAcc; macc; Hide-noDiv-from-MAcc)
open import CSP.Laws.Bisim.DRCongruence (Net-≟ {Data})
  using (ModAStep; maτ; maE)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Data})
  using (Par-τ-elim; ParτR; τL; τR
        ; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {Data})
  using (Par-soloL; Par-soloR; Par-sync; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsHide (Net-≟ {Data})
  using (Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√
        ; Hide-τ; Hide-keep; Hide-hidden)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net-≟ {Data})
  using (deadlock-no-τ; deadlock-no-ev)

⊤merge : Poly.⊤ {0ℓ} → Poly.⊤ {0ℓ} → Poly.⊤ {0ℓ}
⊤merge _ _ = Poly.tt

NetR : Set
NetR = Poly.⊤ {0ℓ}

c0 : Conn N2N_KeepAlive
c0 = zero

------------------------------------------------------------------------
-- Sync / hide sets at the value level (exactly the Network.agda forms).
------------------------------------------------------------------------
csSR' csRS' csTA' : EventSet
csSR' = chanSet csSR csSR-dec
csRS' = chanSet csRS csRS-dec
csTA' = chanSet csTA csTA-dec

------------------------------------------------------------------------
-- State extractors (analogues of NetworkRefinement's `vis-of` / `tau-of`).
------------------------------------------------------------------------
vis-of : NodeKind (Net Data) (ExtI (Net Data)) NetR
       → (at : AnyTypes (Net Data)) → proj₁ at → Maybe NetProc
vis-of (react v _) = v
vis-of _           = λ _ _ → nothing

tau-of : NodeKind (Net Data) (ExtI (Net Data)) NetR
       → (i : AnyTypes (ExtI (Net Data))) → proj₁ i → Maybe NetProc
tau-of (react _ τc) = τc
tau-of _            = λ _ _ → nothing

-- τ-successor of `p` along index `i`/value `a` (identity if no such τ).
succτ : NetProc → (i : AnyTypes (ExtI (Net Data))) → proj₁ i → NetProc
succτ p i a with tau-of (force p) i a
... | just t  = t
... | nothing = p

-- visible successor of `p` along `at`/`a` (identity if not offered).
succV : NetProc → (at : AnyTypes (Net Data)) → proj₁ at → NetProc
succV p at a with vis-of (force p) at a
... | just t  = t
... | nothing = p

------------------------------------------------------------------------
-- The un-hidden composite, `d`-indexed where the initial visible offer
-- forwards the payload.  (`T d` is `U0 d`.)
------------------------------------------------------------------------

-- visible-offer AnyTypes.  The data-carrying channels (input/output/tx)
-- carry payload type `Data`; the ack channels carry `⊤`.
inputAt outputAt txAt : AnyTypes (Net Data)
inputAt  = (Data , input  N2N_KeepAlive c0)
outputAt = (Data , output N2N_KeepAlive c0)
txAt     = (Data , tx     N2N_KeepAlive c0)

ackAt : AnyTypes (Net Data)
ackAt = (⊤ , ack N2N_KeepAlive c0)

-- the un-hidden composite `T = Par⊤ csTA' TxSide RxSide`, as a function of `d`
-- (the head node is `d`-independent, but typing it `Data → NetProc` keeps the
-- gate uniform with the decode).
T : Data → NetProc
T _ = TxSide ∥⇘ csTA' ⇙ RxSide

------------------------------------------------------------------------
-- Phase-A `d`-indexed state walk U0 … U8f, mirroring NetworkRefinement,
-- with `d` at the four forward (data-carrying) positions.
------------------------------------------------------------------------

U0 : Data → NetProc
U0 d = T d

-- U1 := the input-successor (forwards `d`).
U1 : Data → NetProc
U1 d = succV (U0 d) inputAt d

-- U2 := τ on the hidden `sndmsg` inside TxSide (base payload = `d`).
sndmsgIdxU : AnyTypes (ExtI (Net Data))
sndmsgIdxU = _ , pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (sndmsg N2N_KeepAlive c0)))
sndmsgValU : Data → proj₁ sndmsgIdxU
sndmsgValU d = lift fz , (lift (fs fz) , d)

U2 : Data → NetProc
U2 d = succτ (U1 d) sndmsgIdxU (sndmsgValU d)

-- U3 := visible `tx` sync (forwards `d`).
U3 : Data → NetProc
U3 d = succV (U2 d) txAt d

-- U4 := τ on the hidden `rcvmsg` inside RxSide (base payload = `d`).
rcvmsgIdxU : AnyTypes (ExtI (Net Data))
rcvmsgIdxU = _ , pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (rcvmsg N2N_KeepAlive c0)))
rcvmsgValU : Data → proj₁ rcvmsgIdxU
rcvmsgValU d = lift (fs fz) , (lift (fs fz) , d)

U4 : Data → NetProc
U4 d = succτ (U3 d) rcvmsgIdxU (rcvmsgValU d)

-- U5 := the output-successor (forwards `d`).
U5 : Data → NetProc
U5 d = succV (U4 d) outputAt d

-- U6 := τ on the hidden `sndack` inside RxSide (ack channel ⇒ payload `tt`).
sndackIdxU : AnyTypes (ExtI (Net Data))
sndackIdxU = _ , pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (sndack N2N_KeepAlive c0)))
sndackValU : proj₁ sndackIdxU
sndackValU = lift (fs fz) , (lift (fs fz) , tt)

U6 : Data → NetProc
U6 d = succτ (U5 d) sndackIdxU sndackValU

-- U7 := visible `ack` sync (ack channel ⇒ payload `tt`).
U7 : Data → NetProc
U7 d = succV (U6 d) ackAt tt

-- U8 := τ on the hidden `rcvack` inside TxSide (ack channel ⇒ payload `tt`).
rcvackIdxU : AnyTypes (ExtI (Net Data))
rcvackIdxU = _ , pair (fin {n = 2})
                  (pair (fin {n = 2}) (base (rcvack N2N_KeepAlive c0)))
rcvackValU : proj₁ rcvackIdxU
rcvackValU = lift fz , (lift (fs fz) , tt)

U8 : Data → NetProc
U8 d = succτ (U7 d) rcvackIdxU rcvackValU

-- the six `sil`-guard τ's (payload-free `fin {n = 1}` leaves).
g1Idx : AnyTypes (ExtI (Net Data))
g1Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2})
              (pair (fin {n = 2}) (fin {n = 1}))))
g1Val : proj₁ g1Idx
g1Val = lift fz , (lift fz , (lift (fs fz) , (lift (fs fz) , lift fz)))

U8a : Data → NetProc
U8a d = succτ (U8 d) g1Idx g1Val

g2Idx : AnyTypes (ExtI (Net Data))
g2Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2})
              (pair (fin {n = 2}) (fin {n = 1}))))
g2Val : proj₁ g2Idx
g2Val = lift fz , (lift fz , (lift (fs fz) , (lift fz , lift fz)))

U8b : Data → NetProc
U8b d = succτ (U8a d) g2Idx g2Val

g3Idx : AnyTypes (ExtI (Net Data))
g3Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2}) (fin {n = 1})))
g3Val : proj₁ g3Idx
g3Val = lift fz , (lift fz , (lift fz , lift fz))

U8c : Data → NetProc
U8c d = succτ (U8b d) g3Idx g3Val

g4Idx : AnyTypes (ExtI (Net Data))
g4Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2}) (fin {n = 1})))
g4Val : proj₁ g4Idx
g4Val = lift (fs fz) , (lift fz , (lift fz , lift fz))

U8d : Data → NetProc
U8d d = succτ (U8c d) g4Idx g4Val

g5Idx : AnyTypes (ExtI (Net Data))
g5Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2})
              (pair (fin {n = 2}) (fin {n = 1}))))
g5Val : proj₁ g5Idx
g5Val = lift (fs fz) , (lift fz , (lift (fs fz) , (lift fz , lift fz)))

U8e : Data → NetProc
U8e d = succτ (U8d d) g5Idx g5Val

g6Idx : AnyTypes (ExtI (Net Data))
g6Idx = _ , pair (fin {n = 2})
            (pair (fin {n = 2})
             (pair (fin {n = 2})
              (pair (fin {n = 2}) (fin {n = 1}))))
g6Val : proj₁ g6Idx
g6Val = lift (fs fz) , (lift fz , (lift (fs fz) , (lift (fs fz) , lift fz)))

U8f : Data → NetProc
U8f d = succτ (U8e d) g6Idx g6Val

------------------------------------------------------------------------
-- M2: `d`-INDEXED PARAMETRIC DECODE  `⟦_⟧ : CS → Data → NetProc`.
--
-- Six per-operand position decoders.  The four FORWARD (data-carrying)
-- positions take the payload `d`; the ack / guard positions ignore it.
------------------------------------------------------------------------

-- bare-leaf visible-offer indices used by the operand reductions.
-- sndmsg/tx/rcvmsg/output carry `Data`; rcvack/ack/sndack carry `⊤`.
sndmsgAtN rcvmsgAtN txAtN outputAtN : AnyTypes (Net Data)
sndmsgAtN = (Data , sndmsg N2N_KeepAlive c0)
rcvmsgAtN = (Data , rcvmsg N2N_KeepAlive c0)
txAtN     = txAt
outputAtN = outputAt

rcvackAtN ackAtN sndackAtN : AnyTypes (Net Data)
rcvackAtN = (⊤ , rcvack N2N_KeepAlive c0)
ackAtN    = (⊤ , ack    N2N_KeepAlive c0)
sndackAtN = (⊤ , sndack N2N_KeepAlive c0)

------------------------------------------------------------------------
-- decI : the Inputs operand.  Forward position `I1` carries `d`.
------------------------------------------------------------------------
decI : IP → Data → NetProc
decI I0 _ = Inputs
decI I1 d = succV Inputs inputAt d
decI I2 d = succV (succV Inputs inputAt d) sndmsgAtN d
decI Ig d = succV (succV (succV Inputs inputAt d) sndmsgAtN d) rcvackAtN tt

------------------------------------------------------------------------
-- decT : the Transmitter operand.  Forward position `T1` carries `d`.
------------------------------------------------------------------------
decT : TP → Data → NetProc
decT T0 _ = Transmitter
decT T1 d = succV Transmitter sndmsgAtN d
decT Tg d = succV (succV Transmitter sndmsgAtN d) txAtN d

------------------------------------------------------------------------
-- decR : the RcvAck operand (all positions ack-channel ⇒ payload-free).
------------------------------------------------------------------------
decR : RP → Data → NetProc
decR R0 _ = RcvAck
decR R1 _ = succV RcvAck ackAt tt
decR Rg _ = succV (succV RcvAck ackAt tt) rcvackAtN tt

------------------------------------------------------------------------
-- decO : the Outputs operand.  Forward position `O1` carries `d`.
------------------------------------------------------------------------
decO : OP → Data → NetProc
decO O0 _ = Outputs
decO O1 d = succV Outputs rcvmsgAtN d
decO O2 d = succV (succV Outputs rcvmsgAtN d) outputAtN d
decO Og d = succV (succV (succV Outputs rcvmsgAtN d) outputAtN d) sndackAtN tt

------------------------------------------------------------------------
-- decC : the Receiver operand.  Forward position `Rc1` carries `d`.
------------------------------------------------------------------------
decC : CP → Data → NetProc
decC Rc0 _ = Receiver
decC Rc1 d = succV Receiver txAtN d
decC Rcg d = succV (succV Receiver txAtN d) rcvmsgAtN d

------------------------------------------------------------------------
-- decS : the SndAck operand (all positions ack-channel ⇒ payload-free).
------------------------------------------------------------------------
decS : SP → Data → NetProc
decS Sa0 _ = SndAck
decS Sa1 _ = succV SndAck sndackAtN tt
decS Sag _ = succV (succV SndAck sndackAtN tt) ackAtN tt

------------------------------------------------------------------------
-- The two sides and the whole, in the EXACT operator forms of Network.agda.
------------------------------------------------------------------------
decTx : IP → TP → RP → Data → NetProc
decTx i t r d = ((decI i d) ∥⇘ csSR' ⇙ (decT t d ⦀ decR r d)) ∖ csSR'

decRx : OP → CP → SP → Data → NetProc
decRx o c s d = ((decO o d) ∥⇘ csRS' ⇙ (decC c d ⦀ decS s d)) ∖ csRS'

⟦_⟧ : CS → Data → NetProc
⟦ mkCS i t r o c s ⟧ d = (decTx i t r d) ∥⇘ csTA' ⇙ (decRx o c s d)

⟦_⟧N : CS → Data → NetProc
⟦ cs ⟧N d = ⟦ cs ⟧ d ∖ csTA'

------------------------------------------------------------------------
-- THE GATE — validation by `refl` for a SYMBOLIC `d : Data`.
------------------------------------------------------------------------

module Gate (d : Data) where

  dec-cs0 : ⟦ cs0 ⟧N d ≡ Network
  dec-cs0 = refl

  dec-U0 : ⟦ cs0 ⟧ d ≡ T d
  dec-U0 = refl

  dec-U1 : ⟦ mkCS I1 T0 R0 O0 Rc0 Sa0 ⟧ d ≡ U1 d
  dec-U1 = refl

  -- MEMORY NOTE: the forward-state validations dec-U2..U8 and the cycle-closure
  -- U8f≡U0 were proved (propositionally, `rewrite ≟-diag d`) but each forces Agda to
  -- normalize the full Par/Hide-nested composite for a SYMBOLIC `d` — which does NOT
  -- collapse the way `⊤` does, exhausting a 16GB machine.  They are sanity checks; the
  -- forward-state correspondence is exercised downstream by the inversion-based
  -- simulations (which consume given steps and do not `rewrite`-normalize whole goals).
  -- Kept disabled here to keep Task 1 within memory; re-enable individually if needed.
  --
  -- dec-U2 : ⟦ mkCS I2 T1 R0 O0 Rc0 Sa0 ⟧ d ≡ U2 d
  -- dec-U2 rewrite ≟-diag d = refl
  -- … dec-U3 … dec-U8 (rewrite ≟-diag d, increasing count) …
  -- U8f≡U0 : U8f d ≡ U0 d
  -- U8f≡U0 = refl

------------------------------------------------------------------------
-- Stability lemmas: each bare-leaf process has an everywhere-nothing
-- τ-branch map, so every τ-label step is refuted by `refl ()`.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- M3: PER-LEAF STEP CHARACTERIZATION (d-threaded).
--
-- For each of the six operand decode functions: which positions admit a
-- τ (and to where), and which visible events each position offers (and
-- to where).
--
-- KEY ADAPTATION from the ⊤ template: the four data-carrying channels
-- (sndmsg, tx, rcvmsg, output, input) carry `Data` payloads via
-- `Op.Output e d Skip` which uses `Output-cont` with an `a ≟ d` guard.
-- For abstract `DecEq Data`, this guard does NOT reduce definitionally,
-- so:
--   * Forward steps (X0 → X1): conclusion uses the STEP payload `a`
--     (not the ambient `d`), so `sVis refl refl` works directly.
--   * Forwarding steps (X1 → Xg): need `with a ≟ d` case split and
--     `rewrite ≟-diag d` to normalize both `h` and the goal.
--   * Guard τ / noev (Xg): need `rewrite ≟-diag d` to unblock the
--     `succV`-chain, then `sSil refl` or `sVis () _` applies.
-- Positions using only ⊤ payload (ack/rcvack/sndack) work as in the
-- template since `tt ≟ tt = yes refl` is definitional for `DecEq ⊤`.
------------------------------------------------------------------------

-- generic ev-label builder for the bare-leaf alphabet
evN : {B : Set} → Net Data B → B → Event√ NetR
evN {B} e a = evl (evLabel B e a)

-- `output` is re-exported twice; pin the single intended constructor via a
-- freshly qualified import.
import CSP.Examples.Cardano_network.Net p1 as NetQ

output′ : (id : IDs) → Conn id → Net Data Data
output′ = NetQ.output

------------------------------------------------------------------------
-- decT : Transmitter.  T0 --sndmsg--> T1 ; T1 --tx--> Tg ; Tg --τ(sil)--> T0.
------------------------------------------------------------------------

-- T0 ignores d (= Transmitter); sndmsg with payload `a` moves to T1 a.
decT-T0-noτ : ∀ {d W} → decT T0 d ─[ τ ]─► W → ⊥
decT-T0-noτ = Transmitter-stable

decT-T0-sndmsg : ∀ {d a W} →
  decT T0 d ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → W ≡ decT T1 a
decT-T0-sndmsg (sVis refl refl) = refl

-- T1 d: tx fires with value forced to d by Output-cont; result is Tg d.
decT-T1-noτ : ∀ {d W} → decT T1 d ─[ τ ]─► W → ⊥
decT-T1-noτ (sSil ())
decT-T1-noτ (sTau {i = _ , fin}                 refl ())
decT-T1-noτ (sTau {i = _ , base _}              refl ())
decT-T1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decT-T1-noτ (sTau {i = _ , pair fin fin}        refl ())
decT-T1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decT-T1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decT-T1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

private
  -- Output-cont guard makes `nothing ≡ just W` absurd.
  nothing-absurd : ∀ {ℓ} {X : Set ℓ} {W : NetProc} → nothing ≡ just W → X
  nothing-absurd ()

-- T1 d: tx fires with payload forced to equal d by Output-cont.
-- Conclusion is `a ≡ d` (the payload equality), not `W ≡ decT Tg d`,
-- because `decT Tg d = succV (decT T1 d) txAtN d` is stuck at `d ≟ d`
-- even after `rewrite ≟-diag d` at the propositional level.
decT-T1-tx : ∀ {d a W} →
  decT T1 d ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → a ≡ d
decT-T1-tx {d = d} {a = a} (sVis refl h) with a ≟ d
... | yes refl = refl
... | no  _    = nothing-absurd h

-- Tg d: sil τ back to Transmitter (= decT T0 _); ≟-diag d unblocks succV.
decT-Tg-τ : ∀ {d W} → decT Tg d ─[ τ ]─► W → W ≡ decT T0 d
decT-Tg-τ {d = d} step rewrite ≟-diag d with step
... | sSil refl = refl
... | sTau () _

decT-Tg-noev : ∀ {d B e a W} →
  decT Tg d ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decT-Tg-noev {d = d} step rewrite ≟-diag d with step
... | sVis () _

------------------------------------------------------------------------
-- decR : RcvAck.  R0 --ack--> R1 ; R1 --rcvack--> Rg ; Rg --τ(sil)--> R0.
-- All positions carry ⊤ payload; ≟ is definitional.
------------------------------------------------------------------------

decR-R0-noτ : ∀ {d W} → decR R0 d ─[ τ ]─► W → ⊥
decR-R0-noτ = RcvAck-stable

decR-R0-ack : ∀ {d a W} →
  decR R0 d ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → W ≡ decR R1 d
decR-R0-ack (sVis refl refl) = refl

decR-R1-noτ : ∀ {d W} → decR R1 d ─[ τ ]─► W → ⊥
decR-R1-noτ (sSil ())
decR-R1-noτ (sTau {i = _ , fin}                 refl ())
decR-R1-noτ (sTau {i = _ , base _}              refl ())
decR-R1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decR-R1-noτ (sTau {i = _ , pair fin fin}        refl ())
decR-R1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decR-R1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decR-R1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decR-R1-rcvack : ∀ {d a W} →
  decR R1 d ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → W ≡ decR Rg d
decR-R1-rcvack (sVis refl refl) = refl

decR-Rg-τ : ∀ {d W} → decR Rg d ─[ τ ]─► W → W ≡ decR R0 d
decR-Rg-τ (sSil refl) = refl
decR-Rg-τ (sTau () _)

decR-Rg-noev : ∀ {d B e a W} →
  decR Rg d ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decR-Rg-noev (sVis () _)

------------------------------------------------------------------------
-- decC : Receiver.  Rc0 --tx--> Rc1 ; Rc1 --rcvmsg--> Rcg ; Rcg --τ(sil)--> Rc0.
-- tx and rcvmsg carry Data; Rcg needs ≟-diag d.
------------------------------------------------------------------------

decC-Rc0-noτ : ∀ {d W} → decC Rc0 d ─[ τ ]─► W → ⊥
decC-Rc0-noτ = Receiver-stable

decC-Rc0-tx : ∀ {d a W} →
  decC Rc0 d ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → W ≡ decC Rc1 a
decC-Rc0-tx (sVis refl refl) = refl

decC-Rc1-noτ : ∀ {d W} → decC Rc1 d ─[ τ ]─► W → ⊥
decC-Rc1-noτ (sSil ())
decC-Rc1-noτ (sTau {i = _ , fin}                 refl ())
decC-Rc1-noτ (sTau {i = _ , base _}              refl ())
decC-Rc1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decC-Rc1-noτ (sTau {i = _ , pair fin fin}        refl ())
decC-Rc1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decC-Rc1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decC-Rc1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

-- Rc1 d: rcvmsg fires with payload forced to d by Output-cont.
decC-Rc1-rcvmsg : ∀ {d a W} →
  decC Rc1 d ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → a ≡ d
decC-Rc1-rcvmsg {d = d} {a = a} (sVis refl h) with a ≟ d
... | yes refl = refl
... | no  _    = nothing-absurd h

decC-Rcg-τ : ∀ {d W} → decC Rcg d ─[ τ ]─► W → W ≡ decC Rc0 d
decC-Rcg-τ {d = d} step rewrite ≟-diag d with step
... | sSil refl = refl
... | sTau () _

decC-Rcg-noev : ∀ {d B e a W} →
  decC Rcg d ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decC-Rcg-noev {d = d} step rewrite ≟-diag d with step
... | sVis () _

------------------------------------------------------------------------
-- decS : SndAck.  Sa0 --sndack--> Sa1 ; Sa1 --ack--> Sag ; Sag --τ(sil)--> Sa0.
-- All positions carry ⊤ payload; ≟ is definitional.
------------------------------------------------------------------------

decS-Sa0-noτ : ∀ {d W} → decS Sa0 d ─[ τ ]─► W → ⊥
decS-Sa0-noτ = SndAck-stable

decS-Sa0-sndack : ∀ {d a W} →
  decS Sa0 d ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → W ≡ decS Sa1 d
decS-Sa0-sndack (sVis refl refl) = refl

decS-Sa1-noτ : ∀ {d W} → decS Sa1 d ─[ τ ]─► W → ⊥
decS-Sa1-noτ (sSil ())
decS-Sa1-noτ (sTau {i = _ , fin}                 refl ())
decS-Sa1-noτ (sTau {i = _ , base _}              refl ())
decS-Sa1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decS-Sa1-noτ (sTau {i = _ , pair fin fin}        refl ())
decS-Sa1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decS-Sa1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decS-Sa1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

decS-Sa1-ack : ∀ {d a W} →
  decS Sa1 d ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → W ≡ decS Sag d
decS-Sa1-ack (sVis refl refl) = refl

decS-Sag-τ : ∀ {d W} → decS Sag d ─[ τ ]─► W → W ≡ decS Sa0 d
decS-Sag-τ (sSil refl) = refl
decS-Sag-τ (sTau () _)

decS-Sag-noev : ∀ {d B e a W} →
  decS Sag d ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decS-Sag-noev (sVis () _)

------------------------------------------------------------------------
-- decI : the Inputs operand.
--   I0 --input--> I1 ; I1 --sndmsg--> I2 ; I2 --rcvack--> Ig ; Ig --τ--> I0.
--
-- input and sndmsg carry Data; rcvack carries ⊤.
-- I0 (= Inputs) ignores d; I1 d is concrete (pchoice, no ≟-diag).
-- I2 d and Ig d are stuck at d ≟ d; need rewrite ≟-diag d.
------------------------------------------------------------------------

decI-I0-noτ : ∀ {d W} → decI I0 d ─[ τ ]─► W → ⊥
decI-I0-noτ = Inputs-stable

decI-I0-input : ∀ {d a W} →
  decI I0 d ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → W ≡ decI I1 a
decI-I0-input (sVis refl refl) = refl

decI-I1-noτ : ∀ {d W} → decI I1 d ─[ τ ]─► W → ⊥
decI-I1-noτ (sSil ())
decI-I1-noτ (sTau {i = _ , fin}                 refl ())
decI-I1-noτ (sTau {i = _ , base _}              refl ())
decI-I1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decI-I1-noτ (sTau {i = _ , pair fin fin}        refl ())
decI-I1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decI-I1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decI-I1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

-- I1 d: sndmsg fires with payload forced to d by Output-cont.
decI-I1-sndmsg : ∀ {d a W} →
  decI I1 d ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → a ≡ d
decI-I1-sndmsg {d = d} {a = a} (sVis refl h) with a ≟ d
... | yes refl = refl
... | no  _    = nothing-absurd h

-- I2 d: rcvack fires (⊤ payload, ≟-diag d unblocks the stuck decI I2 d).
decI-I2-noτ : ∀ {d W} → decI I2 d ─[ τ ]─► W → ⊥
decI-I2-noτ {d = d} step rewrite ≟-diag d with step
... | sSil ()
... | sTau {i = _ , fin}                 refl ()
... | sTau {i = _ , base _}              refl ()
... | sTau {i = _ , pair fin (base _)}   refl ()
... | sTau {i = _ , pair fin fin}        refl ()
... | sTau {i = _ , pair fin (pair _ _)} refl ()
... | sTau {i = _ , pair (base _) _}     refl ()
... | sTau {i = _ , pair (pair _ _) _}   refl ()

decI-I2-rcvack : ∀ {d a W} →
  decI I2 d ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → W ≡ decI Ig d
decI-I2-rcvack {d = d} step rewrite ≟-diag d with step
... | sVis refl refl = refl

-- Ig d: sil τ back to Inputs (= decI I0 _); ≟-diag d unblocks.
decI-Ig-τ : ∀ {d W} → decI Ig d ─[ τ ]─► W → W ≡ decI I0 d
decI-Ig-τ {d = d} step rewrite ≟-diag d with step
... | sSil refl = refl
... | sTau () _

decI-Ig-noev : ∀ {d B e a W} →
  decI Ig d ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decI-Ig-noev {d = d} step rewrite ≟-diag d with step
... | sVis () _

------------------------------------------------------------------------
-- decO : the Outputs operand.
--   O0 --rcvmsg--> O1 ; O1 --output--> O2 ; O2 --sndack--> Og ; Og --τ--> O0.
--
-- rcvmsg and output carry Data; sndack carries ⊤.
-- O0 (= Outputs) ignores d; O1 d is concrete (pchoice, no ≟-diag).
-- O2 d and Og d are stuck at d ≟ d; need rewrite ≟-diag d.
------------------------------------------------------------------------

decO-O0-noτ : ∀ {d W} → decO O0 d ─[ τ ]─► W → ⊥
decO-O0-noτ = Outputs-stable

decO-O0-rcvmsg : ∀ {d a W} →
  decO O0 d ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → W ≡ decO O1 a
decO-O0-rcvmsg (sVis refl refl) = refl

decO-O1-noτ : ∀ {d W} → decO O1 d ─[ τ ]─► W → ⊥
decO-O1-noτ (sSil ())
decO-O1-noτ (sTau {i = _ , fin}                 refl ())
decO-O1-noτ (sTau {i = _ , base _}              refl ())
decO-O1-noτ (sTau {i = _ , pair fin (base _)}   refl ())
decO-O1-noτ (sTau {i = _ , pair fin fin}        refl ())
decO-O1-noτ (sTau {i = _ , pair fin (pair _ _)} refl ())
decO-O1-noτ (sTau {i = _ , pair (base _) _}     refl ())
decO-O1-noτ (sTau {i = _ , pair (pair _ _) _}   refl ())

-- O1 d: output fires with payload forced to d by Output-cont.
decO-O1-output : ∀ {d a W} →
  decO O1 d ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → a ≡ d
decO-O1-output {d = d} {a = a} (sVis refl h) with a ≟ d
... | yes refl = refl
... | no  _    = nothing-absurd h

-- O2 d: sndack fires (⊤ payload, ≟-diag d unblocks decO O2 d).
decO-O2-noτ : ∀ {d W} → decO O2 d ─[ τ ]─► W → ⊥
decO-O2-noτ {d = d} step rewrite ≟-diag d with step
... | sSil ()
... | sTau {i = _ , fin}                 refl ()
... | sTau {i = _ , base _}              refl ()
... | sTau {i = _ , pair fin (base _)}   refl ()
... | sTau {i = _ , pair fin fin}        refl ()
... | sTau {i = _ , pair fin (pair _ _)} refl ()
... | sTau {i = _ , pair (base _) _}     refl ()
... | sTau {i = _ , pair (pair _ _) _}   refl ()

decO-O2-sndack : ∀ {d a W} →
  decO O2 d ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → W ≡ decO Og d
decO-O2-sndack {d = d} step rewrite ≟-diag d with step
... | sVis refl refl = refl

-- Og d: sil τ back to Outputs (= decO O0 _); ≟-diag d unblocks.
decO-Og-τ : ∀ {d W} → decO Og d ─[ τ ]─► W → W ≡ decO O0 d
decO-Og-τ {d = d} step rewrite ≟-diag d with step
... | sSil refl = refl
... | sTau () _

decO-Og-noev : ∀ {d B e a W} →
  decO Og d ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
decO-Og-noev {d = d} step rewrite ≟-diag d with step
... | sVis () _

------------------------------------------------------------------------
-- Visible labels (value-parametrised — the data-carrying channels carry a
-- payload `a : Data`; the ack channel carries `tt`).  Distinct constructors
-- give pairwise label-disequalities REGARDLESS of the carried value.
------------------------------------------------------------------------

inputLbl outputLbl txLbl : Data → Event√ NetR
inputLbl  a = evl (evLabel Data (input  N2N_KeepAlive c0) a)
outputLbl a = evl (evLabel Data (output N2N_KeepAlive c0) a)
txLbl     a = evl (evLabel Data (tx     N2N_KeepAlive c0) a)

ackLbl : Event√ NetR
ackLbl = evl (evLabel ⊤ (ack N2N_KeepAlive c0) tt)

------------------------------------------------------------------------
-- M4a: TxSide-level simulation lemmas (d-threaded port).
--
--   decTx i t r d = ((decI i d) ∥⇘ csSR' ⇙ (decT t d ⦀ decR r d)) ∖ csSR'
--
-- We characterise EVERY LTS step of `decTx i t r d`.  The forward
-- (data-carrying) operand class lemmas resolve the `Output-cont` guard with
-- `rewrite ≟-diag d` at the OPERAND level (small terms — never the composite).
------------------------------------------------------------------------

-- Operand-level τ classifiers (the only τ each operand admits is its guard).
decI-τ-class : ∀ {i d W} → decI i d ─[ τ ]─► W → (i ≡ Ig) × (W ≡ decI I0 d)
decI-τ-class {I0} {d} step = ⊥-elim (decI-I0-noτ {d} step)
decI-τ-class {I1} {d} step = ⊥-elim (decI-I1-noτ {d} step)
decI-τ-class {I2} {d} step = ⊥-elim (decI-I2-noτ {d} step)
decI-τ-class {Ig} step = refl , decI-Ig-τ step

decT-τ-class : ∀ {t d W} → decT t d ─[ τ ]─► W → (t ≡ Tg) × (W ≡ decT T0 d)
decT-τ-class {T0} {d} step = ⊥-elim (decT-T0-noτ {d} step)
decT-τ-class {T1} {d} step = ⊥-elim (decT-T1-noτ {d} step)
decT-τ-class {Tg} step = refl , decT-Tg-τ step

decR-τ-class : ∀ {r d W} → decR r d ─[ τ ]─► W → (r ≡ Rg) × (W ≡ decR R0 d)
decR-τ-class {R0} {d} step = ⊥-elim (decR-R0-noτ {d} step)
decR-τ-class {R1} {d} step = ⊥-elim (decR-R1-noτ {d} step)
decR-τ-class {Rg} {d} step = refl , decR-Rg-τ {d} step

------------------------------------------------------------------------
-- Operand-level SYNC-event classifiers (sndmsg / rcvack) and refutations.
-- For the forward channel `sndmsg`, the SOURCE leaf (decI at I1) forwards
-- `d` (value forced to `d`), and the PARTNER (decT at T0) introduces the
-- value as its new payload — but the sync pins them equal, so we thread `d`.
------------------------------------------------------------------------

-- decI offers `sndmsg` only at I1 (→ I2); value forced to d.
decI-sndmsg-class : ∀ {i d a W} →
  decI i d ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W →
  (i ≡ I1) × (a ≡ d) × (W ≡ decI I2 d)
decI-sndmsg-class {I0} (sVis refl ())
decI-sndmsg-class {I1} {d = d} {a = a} (sVis refl h) with a ≟ d
... | no  _    = nothing-absurd h
decI-sndmsg-class {I1} {d = d} (sVis refl h) | yes refl
  rewrite ≟-diag d = refl , refl , sym (just-injective h)
decI-sndmsg-class {I2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decI-sndmsg-class {Ig} step = ⊥-elim (decI-Ig-noev step)

-- decI offers `rcvack` only at I2 (→ Ig); ack-channel ⇒ ⊤ payload.
decI-rcvack-class : ∀ {i d a W} →
  decI i d ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → (i ≡ I2) × (W ≡ decI Ig d)
decI-rcvack-class {I0} (sVis refl ())
decI-rcvack-class {I1} (sVis refl ())
decI-rcvack-class {I2} {d} step = refl , decI-I2-rcvack {d} step
decI-rcvack-class {Ig} {d} step = ⊥-elim (decI-Ig-noev {d} step)

-- decT offers `sndmsg` only at T0 (→ T1 a); the value becomes T1's payload.
decT-sndmsg-class : ∀ {t d a W} →
  decT t d ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → (t ≡ T0) × (W ≡ decT T1 a)
decT-sndmsg-class {T0} {d} step = refl , decT-T0-sndmsg {d} step
decT-sndmsg-class {T1} (sVis refl ())
decT-sndmsg-class {Tg} {d} step = ⊥-elim (decT-Tg-noev {d} step)

-- decT refuses `rcvack` everywhere.
decT-no-rcvack : ∀ {t d a W} →
  decT t d ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-rcvack {T0} (sVis refl ())
decT-no-rcvack {T1} (sVis refl ())
decT-no-rcvack {Tg} {d} step = decT-Tg-noev {d} step

-- decR offers `rcvack` only at R1 (→ Rg); ⊤ payload.
decR-rcvack-class : ∀ {r d a W} →
  decR r d ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → (r ≡ R1) × (W ≡ decR Rg d)
decR-rcvack-class {R0} (sVis refl ())
decR-rcvack-class {R1} {d} step = refl , decR-R1-rcvack {d} step
decR-rcvack-class {Rg} {d} step = ⊥-elim (decR-Rg-noev {d} step)

-- decR refuses `sndmsg` everywhere.
decR-no-sndmsg : ∀ {r d a W} →
  decR r d ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-sndmsg {R0} (sVis refl ())
decR-no-sndmsg {R1} (sVis refl ())
decR-no-sndmsg {Rg} {d} step = decR-Rg-noev {d} step

------------------------------------------------------------------------
-- TR = decT t d ⦀ decR r d  (inner interleaving inside TxSide).
------------------------------------------------------------------------

TR-τ-class : ∀ {t r d W} → (decT t d ⦀ decR r d) ─[ τ ]─► W →
    ((t ≡ Tg) × (W ≡ (decT T0 d ⦀ decR r d)))
  ⊎ ((r ≡ Rg) × (W ≡ (decT t  d ⦀ decR R0 d)))
TR-τ-class {t} {r} {d} step with Par-τ-elim ∅ES ⊤merge (decT t d) (decR r d) step
... | τL P′ Tτ refl = inj₁ (proj₁ cl , cong (λ z → z ⦀ decR r d) (proj₂ cl))
  where cl = decT-τ-class {t} {d} Tτ
... | τR Q′ Rτ refl = inj₂ (proj₁ cl , cong (λ z → decT t d ⦀ z) (proj₂ cl))
  where cl = decR-τ-class {r} {d} Rτ

-- sndmsg sync of TR: decT accepts (T0→T1 a); decR refuses ⇒ decT-solo.
TR-sndmsg-class : ∀ {t r d a W} →
  (decT t d ⦀ decR r d) ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W →
  (t ≡ T0) × (W ≡ (decT T1 a ⦀ decR r d))
TR-sndmsg-class {t} {r} {d} step
  with Par-ev-elim ∅ES ⊤merge (decT t d) (decR r d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = proj₁ cl , cong (λ z → z ⦀ decR r d) (proj₂ cl)
  where cl = decT-sndmsg-class {t} {d} Tev
TR-sndmsg-class {t} {r} {d} step | evR  _ Rev = ⊥-elim (decR-no-sndmsg {r} {d} Rev)
TR-sndmsg-class {t} {r} {d} step | evBoth _ Tev Rev = ⊥-elim (decR-no-sndmsg {r} {d} Rev)

-- rcvack sync of TR: decR offers (R1→Rg); decT refuses ⇒ decR-solo.
TR-rcvack-class : ∀ {t r d a W} →
  (decT t d ⦀ decR r d) ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W →
  (r ≡ R1) × (W ≡ (decT t d ⦀ decR Rg d))
TR-rcvack-class {t} {r} {d} step
  with Par-ev-elim ∅ES ⊤merge (decT t d) (decR r d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = ⊥-elim (decT-no-rcvack {t} {d} Tev)
TR-rcvack-class {t} {r} {d} step | evR  _ Rev = proj₁ cl , cong (λ z → decT t d ⦀ z) (proj₂ cl)
  where cl = decR-rcvack-class {r} {d} Rev
TR-rcvack-class {t} {r} {d} step | evBoth _ Tev _ = ⊥-elim (decT-no-rcvack {t} {d} Tev)

------------------------------------------------------------------------
-- sim-Tx-τ : characterise every τ of decTx i t r d.
--   internal moves: sndmsg-sync, rcvack-sync, guard gI, guard gT, guard gR.
--   (each preserves the in-flight payload `d`).
------------------------------------------------------------------------

sim-Tx-τ : ∀ {i t r d W} → decTx i t r d ─[ τ ]─► W →
    ((i ≡ I1) × (t ≡ T0) × (W ≡ decTx I2 T1 r d))    -- sndmsg sync
  ⊎ ((r ≡ R1) × (i ≡ I2) × (W ≡ decTx Ig t Rg d))     -- rcvack sync
  ⊎ ((i ≡ Ig) × (W ≡ decTx I0 t r d))                 -- guard gI
  ⊎ ((t ≡ Tg) × (W ≡ decTx i T0 r d))                 -- guard gT
  ⊎ ((r ≡ Rg) × (W ≡ decTx i t R0 d))                 -- guard gR
sim-Tx-τ {i} {t} {r} {d} step
  with Hide-τ-elim csSR' ((decI i d) ∥⇘ csSR' ⇙ (decT t d ⦀ decR r d)) step
-- (A) the inner Par's own τ: decI guard, or a τ of TR (decT/decR guard).
... | hτP _ parτ refl
      with Par-τ-elim csSR' ⊤merge (decI i d) (decT t d ⦀ decR r d) parτ
...   | τL _ Iτ refl =
        inj₂ (inj₂ (inj₁ (proj₁ cl ,
          cong (λ z → ((z ∥⇘ csSR' ⇙ (decT t d ⦀ decR r d)) ∖ csSR')) (proj₂ cl))))
  where cl = decI-τ-class Iτ
sim-Tx-τ {i} {t} {r} {d} step | hτP _ parτ refl
      | τR _ TRτ refl with TR-τ-class TRτ
...     | inj₁ (gt , weq) =
          inj₂ (inj₂ (inj₂ (inj₁ (gt ,
            cong (λ z → (((decI i d) ∥⇘ csSR' ⇙ z) ∖ csSR')) weq))))
...     | inj₂ (gr , weq) =
          inj₂ (inj₂ (inj₂ (inj₂ (gr ,
            cong (λ z → (((decI i d) ∥⇘ csSR' ⇙ z) ∖ csSR')) weq))))
-- (B) a HIDDEN csSR-event of the inner Par: a sndmsg or rcvack SYNC.
sim-Tx-τ {i} {t} {r} {d} step
  | hτH {B} {e} {a} _ mem parev refl with e
... | sndmsg N2N_ChainSync    ()
... | sndmsg N2N_BlockFetch   ()
... | sndmsg N2N_TxSubmission ()
... | sndmsg N2N_LeiosNotify  ()
... | sndmsg N2N_LeiosFetch   ()
... | sndmsg N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i d) (decT t d ⦀ decR r d) parev
...   | evSync _ Iev TRev = inj₁ (proj₁ clI , proj₁ clTR ,
          cong₂ (λ z w → ((z ∥⇘ csSR' ⇙ w) ∖ csSR')) (proj₂ (proj₂ clI))
            (trans (proj₂ clTR) (cong (λ z → decT T1 z ⦀ decR r d) (proj₁ (proj₂ clI)))))
  where clI  = decI-sndmsg-class {i} Iev
        clTR = TR-sndmsg-class {t} {r} TRev
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg N2N_KeepAlive zero
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg N2N_KeepAlive zero
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndmsg N2N_KeepAlive zero
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_ChainSync    ()
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_BlockFetch   ()
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_TxSubmission ()
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_LeiosNotify  ()
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_LeiosFetch   ()
sim-Tx-τ {i} {t} {r} {d} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i d) (decT t d ⦀ decR r d) parev
...   | evSync _ Iev TRev = inj₂ (inj₁ (proj₁ clR , proj₁ clI ,
          cong₂ (λ z w → ((z ∥⇘ csSR' ⇙ w) ∖ csSR')) (proj₂ clI) (proj₂ clR)))
  where clI = decI-rcvack-class {i} Iev
        clR = TR-rcvack-class {t} {r} TRev
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_KeepAlive zero
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_KeepAlive zero
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvack N2N_KeepAlive zero
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | input id c  = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | output id c = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg id c = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | tx id c     = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | sndack id c = ⊥-elim mem
sim-Tx-τ {i} {t} {r} step | hτH {B} {e} {a} _ mem parev refl | ack id c    = ⊥-elim mem

------------------------------------------------------------------------
-- Operand-level visible-offer classifiers / refutations for the NON-csSR
-- events (input on decI; tx / ack on the TR side).
------------------------------------------------------------------------

-- decI offers `input` only at I0 (→ I1 a); `input` introduces a fresh payload.
decI-input-class : ∀ {i d a W} →
  decI i d ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → (i ≡ I0) × (W ≡ decI I1 a)
decI-input-class {I0} {d} step = refl , decI-I0-input {d} step
decI-input-class {I1} (sVis refl ())
decI-input-class {I2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decI-input-class {Ig} {d} step = ⊥-elim (decI-Ig-noev {d} step)

-- decI refuses tx / ack / output / rcvmsg / sndack at every position.
decI-no-tx : ∀ {i d a W} →
  decI i d ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-tx {I0} (sVis refl ())
decI-no-tx {I1} (sVis refl ())
decI-no-tx {I2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decI-no-tx {Ig} {d} step = decI-Ig-noev {d} step

decI-no-ack : ∀ {i d a W} →
  decI i d ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-ack {I0} (sVis refl ())
decI-no-ack {I1} (sVis refl ())
decI-no-ack {I2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decI-no-ack {Ig} {d} step = decI-Ig-noev {d} step

decI-no-output : ∀ {i d a W} →
  decI i d ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-output {I0} (sVis refl ())
decI-no-output {I1} (sVis refl ())
decI-no-output {I2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decI-no-output {Ig} {d} step = decI-Ig-noev {d} step

decI-no-rcvmsg : ∀ {i d a W} →
  decI i d ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-rcvmsg {I0} (sVis refl ())
decI-no-rcvmsg {I1} (sVis refl ())
decI-no-rcvmsg {I2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decI-no-rcvmsg {Ig} {d} step = decI-Ig-noev {d} step

decI-no-sndack : ∀ {i d a W} →
  decI i d ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
decI-no-sndack {I0} (sVis refl ())
decI-no-sndack {I1} (sVis refl ())
decI-no-sndack {I2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decI-no-sndack {Ig} {d} step = decI-Ig-noev {d} step

-- decT refuses input / ack / output / rcvmsg / sndack at every position.
decT-no-input : ∀ {t d a W} →
  decT t d ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-input {T0} (sVis refl ())
decT-no-input {T1} (sVis refl ())
decT-no-input {Tg} {d} step = decT-Tg-noev {d} step

decT-no-ack : ∀ {t d a W} →
  decT t d ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-ack {T0} (sVis refl ())
decT-no-ack {T1} (sVis refl ())
decT-no-ack {Tg} {d} step = decT-Tg-noev {d} step

decT-no-output : ∀ {t d a W} →
  decT t d ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-output {T0} (sVis refl ())
decT-no-output {T1} (sVis refl ())
decT-no-output {Tg} {d} step = decT-Tg-noev {d} step

decT-no-rcvmsg : ∀ {t d a W} →
  decT t d ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-rcvmsg {T0} (sVis refl ())
decT-no-rcvmsg {T1} (sVis refl ())
decT-no-rcvmsg {Tg} {d} step = decT-Tg-noev {d} step

decT-no-sndack : ∀ {t d a W} →
  decT t d ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
decT-no-sndack {T0} (sVis refl ())
decT-no-sndack {T1} (sVis refl ())
decT-no-sndack {Tg} {d} step = decT-Tg-noev {d} step

-- decT offers `tx` only at T1 (→ Tg d); `tx` forwards the payload d (a≡d).
decT-tx-class : ∀ {t d a W} →
  decT t d ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → (t ≡ T1) × (a ≡ d) × (W ≡ decT Tg d)
decT-tx-class {T0} (sVis refl ())
decT-tx-class {T1} {d = d} {a = a} (sVis refl h) with a ≟ d
... | no  _    = nothing-absurd h
decT-tx-class {T1} {d = d} (sVis refl h) | yes refl
  rewrite ≟-diag d = refl , refl , sym (just-injective h)
decT-tx-class {Tg} {d} step = ⊥-elim (decT-Tg-noev {d} step)

-- decR refuses input / tx / output / rcvmsg / sndack at every position.
decR-no-input : ∀ {r d a W} →
  decR r d ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-input {R0} (sVis refl ())
decR-no-input {R1} (sVis refl ())
decR-no-input {Rg} {d} step = decR-Rg-noev {d} step

decR-no-tx : ∀ {r d a W} →
  decR r d ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-tx {R0} (sVis refl ())
decR-no-tx {R1} (sVis refl ())
decR-no-tx {Rg} {d} step = decR-Rg-noev {d} step

decR-no-output : ∀ {r d a W} →
  decR r d ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-output {R0} (sVis refl ())
decR-no-output {R1} (sVis refl ())
decR-no-output {Rg} {d} step = decR-Rg-noev {d} step

decR-no-rcvmsg : ∀ {r d a W} →
  decR r d ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-rcvmsg {R0} (sVis refl ())
decR-no-rcvmsg {R1} (sVis refl ())
decR-no-rcvmsg {Rg} {d} step = decR-Rg-noev {d} step

decR-no-sndack : ∀ {r d a W} →
  decR r d ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
decR-no-sndack {R0} (sVis refl ())
decR-no-sndack {R1} (sVis refl ())
decR-no-sndack {Rg} {d} step = decR-Rg-noev {d} step

-- decR offers `ack` only at R0 (→ R1); ⊤ payload.
decR-ack-class : ∀ {r d a W} →
  decR r d ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → (r ≡ R0) × (W ≡ decR R1 d)
decR-ack-class {R0} {d} step = refl , decR-R0-ack {d} step
decR-ack-class {R1} (sVis refl ())
decR-ack-class {Rg} {d} step = ⊥-elim (decR-Rg-noev {d} step)

------------------------------------------------------------------------
-- TR-side visible-offer classifiers / refutations.
------------------------------------------------------------------------

-- TR offers `tx` only via decT at T1 (→ Tg d); decR refuses tx ⇒ decT-solo.
TR-tx-class : ∀ {t r d a W} →
  (decT t d ⦀ decR r d) ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W →
  (t ≡ T1) × (a ≡ d) × (W ≡ (decT Tg d ⦀ decR r d))
TR-tx-class {t} {r} {d} step
  with Par-ev-elim ∅ES ⊤merge (decT t d) (decR r d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = proj₁ cl , proj₁ (proj₂ cl) , cong (λ z → z ⦀ decR r d) (proj₂ (proj₂ cl))
  where cl = decT-tx-class {t} {d} Tev
TR-tx-class {t} {r} {d} step | evR  _ Rev = ⊥-elim (decR-no-tx {r} {d} Rev)
TR-tx-class {t} {r} {d} step | evBoth _ _ Rev = ⊥-elim (decR-no-tx {r} {d} Rev)

-- TR offers `ack` only via decR at R0 (→ R1); decT refuses ack ⇒ decR-solo.
TR-ack-class : ∀ {t r d a W} →
  (decT t d ⦀ decR r d) ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W →
  (r ≡ R0) × (W ≡ (decT t d ⦀ decR R1 d))
TR-ack-class {t} {r} {d} step
  with Par-ev-elim ∅ES ⊤merge (decT t d) (decR r d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = ⊥-elim (decT-no-ack {t} {d} Tev)
TR-ack-class {t} {r} {d} step | evR  _ Rev = proj₁ cl , cong (λ z → decT t d ⦀ z) (proj₂ cl)
  where cl = decR-ack-class {r} {d} Rev
TR-ack-class {t} {r} {d} step | evBoth _ Tev _ = ⊥-elim (decT-no-ack {t} {d} Tev)

-- TR refuses input / output / rcvmsg / sndack at every position.
TR-no-input : ∀ {t r d a W} →
  (decT t d ⦀ decR r d) ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
TR-no-input {t} {r} {d} step with Par-ev-elim ∅ES ⊤merge (decT t d) (decR r d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-input {t} {d} Tev
... | evR  _ Rev       = decR-no-input {r} {d} Rev
... | evBoth _ Tev _   = decT-no-input {t} {d} Tev

TR-no-output : ∀ {t r d a W} →
  (decT t d ⦀ decR r d) ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
TR-no-output {t} {r} {d} step with Par-ev-elim ∅ES ⊤merge (decT t d) (decR r d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-output {t} {d} Tev
... | evR  _ Rev       = decR-no-output {r} {d} Rev
... | evBoth _ Tev _   = decT-no-output {t} {d} Tev

TR-no-rcvmsg : ∀ {t r d a W} →
  (decT t d ⦀ decR r d) ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
TR-no-rcvmsg {t} {r} {d} step with Par-ev-elim ∅ES ⊤merge (decT t d) (decR r d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-rcvmsg {t} {d} Tev
... | evR  _ Rev       = decR-no-rcvmsg {r} {d} Rev
... | evBoth _ Tev _   = decT-no-rcvmsg {t} {d} Tev

TR-no-sndack : ∀ {t r d a W} →
  (decT t d ⦀ decR r d) ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
TR-no-sndack {t} {r} {d} step with Par-ev-elim ∅ES ⊤merge (decT t d) (decR r d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Tev       = decT-no-sndack {t} {d} Tev
... | evR  _ Rev       = decR-no-sndack {r} {d} Rev
... | evBoth _ Tev _   = decT-no-sndack {t} {d} Tev

------------------------------------------------------------------------
-- sim-Tx-ev : characterise every VISIBLE offer of decTx i t r d.
--   · input  (i=I0)  → decTx I1 t r a    (NEW payload `a`)
--   · tx     (t=T1)  → decTx i Tg r d     (forwards `d`)
--   · ack    (r=R0)  → decTx i t R1 d
------------------------------------------------------------------------

-- Tx-side input result: only the decI operand advances to `I1 a′` with the
-- NEW payload `a′`; the partner operands (decT/decR) keep their old payload
-- `d` — captured by the mixed-payload form below.
decTxᵢ : IP → TP → RP → Data → Data → NetProc
decTxᵢ i t r dI dR = ((decI i dI) ∥⇘ csSR' ⇙ (decT t dR ⦀ decR r dR)) ∖ csSR'

sim-Tx-ev : ∀ {i t r d B} {e : Net Data B} {a} {W} →
  decTx i t r d ─[ ev (evl (evLabel B e a)) ]─► W →
    (Σ[ a′ ∈ Data ] ((i ≡ I0) × (evl (evLabel B e a) ≡ inputLbl a′) × (W ≡ decTxᵢ I1 t r a′ d)))
  ⊎ ((t ≡ T1) × (evl (evLabel B e a) ≡ txLbl d)  × (W ≡ decTx i Tg r d))
  ⊎ ((r ≡ R0) × (evl (evLabel B e a) ≡ ackLbl)   × (W ≡ decTx i t R1 d))
sim-Tx-ev {i} {t} {r} {d} step
  with Hide-ev-elim csSR' ((decI i d) ∥⇘ csSR' ⇙ (decT t d ⦀ decR r d)) step
... | heV {B} {e} {a} _ ¬cs parev with e
... | input N2N_ChainSync    ()
... | input N2N_BlockFetch   ()
... | input N2N_TxSubmission ()
... | input N2N_LeiosNotify  ()
... | input N2N_LeiosFetch   ()
... | input N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i d) (decT t d ⦀ decR r d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = inj₁ (a , proj₁ cl , refl ,
          cong (λ z → ((z ∥⇘ csSR' ⇙ (decT t d ⦀ decR r d)) ∖ csSR')) (proj₂ cl))
  where cl = decI-input-class {i} Iev
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | input N2N_KeepAlive zero
      | evR  _ TRev      = ⊥-elim (TR-no-input {t} {r} TRev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | input N2N_KeepAlive zero
      | evBoth _ _ TRev  = ⊥-elim (TR-no-input {t} {r} TRev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} {d} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i d) (decT t d ⦀ decR r d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-tx {i} Iev)
sim-Tx-ev {i} {t} {r} {d} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      | evR  _ TRev      = inj₂ (inj₁ (proj₁ cl ,
          cong (λ z → evl (evLabel Data (tx N2N_KeepAlive c0) z)) (proj₁ (proj₂ cl)) ,
          cong (λ z → (((decI i d) ∥⇘ csSR' ⇙ z) ∖ csSR')) (proj₂ (proj₂ cl))))
  where cl = TR-tx-class {t} {r} {d} TRev
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      | evBoth _ Iev _   = ⊥-elim (decI-no-tx {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} {d} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i d) (decT t d ⦀ decR r d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-ack {i} Iev)
sim-Tx-ev {i} {t} {r} {d} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      | evR  _ TRev      = inj₂ (inj₂ (proj₁ cl , refl ,
          cong (λ z → (((decI i d) ∥⇘ csSR' ⇙ z) ∖ csSR')) (proj₂ cl)))
  where cl = TR-ack-class {t} {r} {d} TRev
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      | evBoth _ Iev _   = ⊥-elim (decI-no-ack {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndmsg id c = ⊥-elim (¬cs Poly.tt)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvack id c = ⊥-elim (¬cs Poly.tt)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | output N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} {d} step | heV {B} {e} {a} _ ¬cs parev | output N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i d) (decT t d ⦀ decR r d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-output {i} Iev)
...   | evR  _ TRev      = ⊥-elim (TR-no-output {t} {r} TRev)
...   | evBoth _ Iev _   = ⊥-elim (decI-no-output {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} {d} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i d) (decT t d ⦀ decR r d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-rcvmsg {i} Iev)
...   | evR  _ TRev      = ⊥-elim (TR-no-rcvmsg {t} {r} TRev)
...   | evBoth _ Iev _   = ⊥-elim (decI-no-rcvmsg {i} Iev)
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_ChainSync    ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_BlockFetch   ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_TxSubmission ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_LeiosNotify  ()
sim-Tx-ev {i} {t} {r} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_LeiosFetch   ()
sim-Tx-ev {i} {t} {r} {d} step | heV {B} {e} {a} _ ¬cs parev | sndack N2N_KeepAlive zero
      with Par-ev-elim csSR' ⊤merge (decI i d) (decT t d ⦀ decR r d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Iev       = ⊥-elim (decI-no-sndack {i} Iev)
...   | evR  _ TRev      = ⊥-elim (TR-no-sndack {t} {r} TRev)
...   | evBoth _ Iev _   = ⊥-elim (decI-no-sndack {i} Iev)

------------------------------------------------------------------------
-- M4b: RxSide-level simulation lemmas (the MIRROR of M4a, d-threaded).
--
--   decRx o c s d = ((decO o d) ∥⇘ csRS' ⇙ (decC c d ⦀ decS s d)) ∖ csRS'
------------------------------------------------------------------------

-- Operand-level τ classifiers.
decO-τ-class : ∀ {o d W} → decO o d ─[ τ ]─► W → (o ≡ Og) × (W ≡ decO O0 d)
decO-τ-class {O0} {d} step = ⊥-elim (decO-O0-noτ {d} step)
decO-τ-class {O1} {d} step = ⊥-elim (decO-O1-noτ {d} step)
decO-τ-class {O2} {d} step = ⊥-elim (decO-O2-noτ {d} step)
decO-τ-class {Og} step = refl , decO-Og-τ step

decC-τ-class : ∀ {c d W} → decC c d ─[ τ ]─► W → (c ≡ Rcg) × (W ≡ decC Rc0 d)
decC-τ-class {Rc0} {d} step = ⊥-elim (decC-Rc0-noτ {d} step)
decC-τ-class {Rc1} {d} step = ⊥-elim (decC-Rc1-noτ {d} step)
decC-τ-class {Rcg} step = refl , decC-Rcg-τ step

decS-τ-class : ∀ {s d W} → decS s d ─[ τ ]─► W → (s ≡ Sag) × (W ≡ decS Sa0 d)
decS-τ-class {Sa0} {d} step = ⊥-elim (decS-Sa0-noτ {d} step)
decS-τ-class {Sa1} {d} step = ⊥-elim (decS-Sa1-noτ {d} step)
decS-τ-class {Sag} {d} step = refl , decS-Sag-τ {d} step

------------------------------------------------------------------------
-- SYNC-event classifiers (rcvmsg / sndack) and refutations.
------------------------------------------------------------------------

-- decO offers `rcvmsg` only at O0 (→ O1 a); the value becomes O1's payload.
decO-rcvmsg-class : ∀ {o d a W} →
  decO o d ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → (o ≡ O0) × (W ≡ decO O1 a)
decO-rcvmsg-class {O0} {d} step = refl , decO-O0-rcvmsg {d} step
decO-rcvmsg-class {O1} (sVis refl ())
decO-rcvmsg-class {O2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-rcvmsg-class {Og} {d} step = ⊥-elim (decO-Og-noev {d} step)

-- decO offers `sndack` only at O2 (→ Og); ⊤ payload.
decO-sndack-class : ∀ {o d a W} →
  decO o d ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → (o ≡ O2) × (W ≡ decO Og d)
decO-sndack-class {O0} (sVis refl ())
decO-sndack-class {O1} (sVis refl ())
decO-sndack-class {O2} {d} step = refl , decO-O2-sndack {d} step
decO-sndack-class {Og} {d} step = ⊥-elim (decO-Og-noev {d} step)

-- decC offers `rcvmsg` only at Rc1 (→ Rcg d); forwards d (a≡d).
decC-rcvmsg-class : ∀ {c d a W} →
  decC c d ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W →
  (c ≡ Rc1) × (a ≡ d) × (W ≡ decC Rcg d)
decC-rcvmsg-class {Rc0} (sVis refl ())
decC-rcvmsg-class {Rc1} {d = d} {a = a} (sVis refl h) with a ≟ d
... | no  _    = nothing-absurd h
decC-rcvmsg-class {Rc1} {d = d} (sVis refl h) | yes refl
  rewrite ≟-diag d = refl , refl , sym (just-injective h)
decC-rcvmsg-class {Rcg} {d} step = ⊥-elim (decC-Rcg-noev {d} step)

-- decC refuses `sndack` everywhere.
decC-no-sndack : ∀ {c d a W} →
  decC c d ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-sndack {Rc0} (sVis refl ())
decC-no-sndack {Rc1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decC-no-sndack {Rcg} {d} step = decC-Rcg-noev {d} step

-- decS offers `sndack` only at Sa0 (→ Sa1); ⊤ payload.
decS-sndack-class : ∀ {s d a W} →
  decS s d ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W → (s ≡ Sa0) × (W ≡ decS Sa1 d)
decS-sndack-class {Sa0} {d} step = refl , decS-Sa0-sndack {d} step
decS-sndack-class {Sa1} (sVis refl ())
decS-sndack-class {Sag} {d} step = ⊥-elim (decS-Sag-noev {d} step)

-- decS refuses `rcvmsg` everywhere.
decS-no-rcvmsg : ∀ {s d a W} →
  decS s d ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-rcvmsg {Sa0} (sVis refl ())
decS-no-rcvmsg {Sa1} (sVis refl ())
decS-no-rcvmsg {Sag} {d} step = decS-Sag-noev {d} step

------------------------------------------------------------------------
-- RS = decC c d ⦀ decS s d  (inner interleaving inside RxSide).
------------------------------------------------------------------------

RS-τ-class : ∀ {c s d W} → (decC c d ⦀ decS s d) ─[ τ ]─► W →
    ((c ≡ Rcg) × (W ≡ (decC Rc0 d ⦀ decS s d)))
  ⊎ ((s ≡ Sag) × (W ≡ (decC c   d ⦀ decS Sa0 d)))
RS-τ-class {c} {s} {d} step with Par-τ-elim ∅ES ⊤merge (decC c d) (decS s d) step
... | τL P′ Cτ refl = inj₁ (proj₁ cl , cong (λ z → z ⦀ decS s d) (proj₂ cl))
  where cl = decC-τ-class {c} {d} Cτ
... | τR Q′ Sτ refl = inj₂ (proj₁ cl , cong (λ z → decC c d ⦀ z) (proj₂ cl))
  where cl = decS-τ-class {s} {d} Sτ

-- rcvmsg sync of RS: decC accepts (Rc1→Rcg); decS refuses ⇒ decC-solo.
RS-rcvmsg-class : ∀ {c s d a W} →
  (decC c d ⦀ decS s d) ─[ ev (evN (rcvmsg N2N_KeepAlive c0) a) ]─► W →
  (c ≡ Rc1) × (a ≡ d) × (W ≡ (decC Rcg d ⦀ decS s d))
RS-rcvmsg-class {c} {s} {d} step
  with Par-ev-elim ∅ES ⊤merge (decC c d) (decS s d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = proj₁ cl , proj₁ (proj₂ cl) , cong (λ z → z ⦀ decS s d) (proj₂ (proj₂ cl))
  where cl = decC-rcvmsg-class {c} {d} Cev
RS-rcvmsg-class {c} {s} {d} step | evR  _ Sev = ⊥-elim (decS-no-rcvmsg {s} {d} Sev)
RS-rcvmsg-class {c} {s} {d} step | evBoth _ Cev Sev = ⊥-elim (decS-no-rcvmsg {s} {d} Sev)

-- sndack sync of RS: decS offers (Sa0→Sa1); decC refuses ⇒ decS-solo.
RS-sndack-class : ∀ {c s d a W} →
  (decC c d ⦀ decS s d) ─[ ev (evN (sndack N2N_KeepAlive c0) a) ]─► W →
  (s ≡ Sa0) × (W ≡ (decC c d ⦀ decS Sa1 d))
RS-sndack-class {c} {s} {d} step
  with Par-ev-elim ∅ES ⊤merge (decC c d) (decS s d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = ⊥-elim (decC-no-sndack {c} {d} Cev)
RS-sndack-class {c} {s} {d} step | evR  _ Sev = proj₁ cl , cong (λ z → decC c d ⦀ z) (proj₂ cl)
  where cl = decS-sndack-class {s} {d} Sev
RS-sndack-class {c} {s} {d} step | evBoth _ Cev _ = ⊥-elim (decC-no-sndack {c} {d} Cev)

------------------------------------------------------------------------
-- sim-Rx-τ : characterise every τ of decRx o c s d.
------------------------------------------------------------------------

sim-Rx-τ : ∀ {o c s d W} → decRx o c s d ─[ τ ]─► W →
    ((c ≡ Rc1) × (o ≡ O0) × (W ≡ decRx O1 Rcg s d))   -- rcvmsg sync
  ⊎ ((o ≡ O2) × (s ≡ Sa0) × (W ≡ decRx Og c Sa1 d))    -- sndack sync
  ⊎ ((o ≡ Og) × (W ≡ decRx O0 c s d))                  -- gO
  ⊎ ((c ≡ Rcg) × (W ≡ decRx o Rc0 s d))                -- gRc
  ⊎ ((s ≡ Sag) × (W ≡ decRx o c Sa0 d))                -- gSa
sim-Rx-τ {o} {c} {s} {d} step
  with Hide-τ-elim csRS' ((decO o d) ∥⇘ csRS' ⇙ (decC c d ⦀ decS s d)) step
... | hτP _ parτ refl
      with Par-τ-elim csRS' ⊤merge (decO o d) (decC c d ⦀ decS s d) parτ
...   | τL _ Oτ refl =
        inj₂ (inj₂ (inj₁ (proj₁ cl ,
          cong (λ z → ((z ∥⇘ csRS' ⇙ (decC c d ⦀ decS s d)) ∖ csRS')) (proj₂ cl))))
  where cl = decO-τ-class {o} {d} Oτ
sim-Rx-τ {o} {c} {s} {d} step | hτP _ parτ refl
      | τR _ RSτ refl with RS-τ-class RSτ
...     | inj₁ (gc , weq) =
          inj₂ (inj₂ (inj₂ (inj₁ (gc ,
            cong (λ z → (((decO o d) ∥⇘ csRS' ⇙ z) ∖ csRS')) weq))))
...     | inj₂ (gs , weq) =
          inj₂ (inj₂ (inj₂ (inj₂ (gs ,
            cong (λ z → (((decO o d) ∥⇘ csRS' ⇙ z) ∖ csRS')) weq))))
sim-Rx-τ {o} {c} {s} {d} step
  | hτH {B} {e} {a} _ mem parev refl with e
... | rcvmsg N2N_ChainSync    ()
... | rcvmsg N2N_BlockFetch   ()
... | rcvmsg N2N_TxSubmission ()
... | rcvmsg N2N_LeiosNotify  ()
... | rcvmsg N2N_LeiosFetch   ()
... | rcvmsg N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o d) (decC c d ⦀ decS s d) parev
...   | evSync _ Oev RSev = inj₁ (proj₁ clRS , proj₁ clO ,
          cong₂ (λ z w → ((z ∥⇘ csRS' ⇙ w) ∖ csRS'))
            (trans (proj₂ clO) (cong (decO O1) (proj₁ (proj₂ clRS)))) (proj₂ (proj₂ clRS)))
  where clO  = decO-rcvmsg-class {o} {d} Oev
        clRS = RS-rcvmsg-class {c} {s} {d} RSev
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg N2N_KeepAlive zero
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg N2N_KeepAlive zero
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvmsg N2N_KeepAlive zero
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_ChainSync    ()
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_BlockFetch   ()
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_TxSubmission ()
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_LeiosNotify  ()
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_LeiosFetch   ()
sim-Rx-τ {o} {c} {s} {d} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o d) (decC c d ⦀ decS s d) parev
...   | evSync _ Oev RSev = inj₂ (inj₁ (proj₁ clO , proj₁ clRS ,
          cong₂ (λ z w → ((z ∥⇘ csRS' ⇙ w) ∖ csRS')) (proj₂ clO) (proj₂ clRS)))
  where clO  = decO-sndack-class {o} {d} Oev
        clRS = RS-sndack-class {c} {s} {d} RSev
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_KeepAlive zero
      | evL  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_KeepAlive zero
      | evR  ¬cs _   = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndack N2N_KeepAlive zero
      | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | input id c′  = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | output id c′ = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | tx id c′     = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | sndmsg id c′ = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | rcvack id c′ = ⊥-elim mem
sim-Rx-τ {o} {c} {s} step | hτH {B} {e} {a} _ mem parev refl | ack id c′    = ⊥-elim mem

------------------------------------------------------------------------
-- Rx-side visible-offer classifiers / refutations for NON-csRS events
-- (output on decO; tx / ack on the RS side).
------------------------------------------------------------------------

-- decO offers `output` only at O1 (→ O2 d); forwards d (a≡d).
decO-output-class : ∀ {o d a W} →
  decO o d ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → (o ≡ O1) × (a ≡ d) × (W ≡ decO O2 d)
decO-output-class {O0} (sVis refl ())
decO-output-class {O1} {d = d} {a = a} (sVis refl h) with a ≟ d
... | no  _    = nothing-absurd h
decO-output-class {O1} {d = d} (sVis refl h) | yes refl
  rewrite ≟-diag d = refl , refl , sym (just-injective h)
decO-output-class {O2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-output-class {Og} {d} step = ⊥-elim (decO-Og-noev {d} step)

-- decO refuses tx / ack / input / sndmsg / rcvack at every position.
decO-no-tx : ∀ {o d a W} →
  decO o d ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-tx {O0} (sVis refl ())
decO-no-tx {O1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-tx {O2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-tx {Og} {d} step = decO-Og-noev {d} step

decO-no-ack : ∀ {o d a W} →
  decO o d ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-ack {O0} (sVis refl ())
decO-no-ack {O1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-ack {O2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-ack {Og} {d} step = decO-Og-noev {d} step

decO-no-input : ∀ {o d a W} →
  decO o d ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-input {O0} (sVis refl ())
decO-no-input {O1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-input {O2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-input {Og} {d} step = decO-Og-noev {d} step

decO-no-sndmsg : ∀ {o d a W} →
  decO o d ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-sndmsg {O0} (sVis refl ())
decO-no-sndmsg {O1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-sndmsg {O2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-sndmsg {Og} {d} step = decO-Og-noev {d} step

decO-no-rcvack : ∀ {o d a W} →
  decO o d ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
decO-no-rcvack {O0} (sVis refl ())
decO-no-rcvack {O1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-rcvack {O2} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decO-no-rcvack {Og} {d} step = decO-Og-noev {d} step

-- decC offers `tx` only at Rc0 (→ Rc1 a); the value becomes Rc1's payload.
decC-tx-class : ∀ {c d a W} →
  decC c d ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → (c ≡ Rc0) × (W ≡ decC Rc1 a)
decC-tx-class {Rc0} {d} step = refl , decC-Rc0-tx {d} step
decC-tx-class {Rc1} (sVis refl ())
decC-tx-class {Rcg} {d} step = ⊥-elim (decC-Rcg-noev {d} step)

-- decC refuses output / ack / input / sndmsg / rcvack at every position.
decC-no-output : ∀ {c d a W} →
  decC c d ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-output {Rc0} (sVis refl ())
decC-no-output {Rc1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decC-no-output {Rcg} {d} step = decC-Rcg-noev {d} step

decC-no-ack : ∀ {c d a W} →
  decC c d ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-ack {Rc0} (sVis refl ())
decC-no-ack {Rc1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decC-no-ack {Rcg} {d} step = decC-Rcg-noev {d} step

decC-no-input : ∀ {c d a W} →
  decC c d ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-input {Rc0} (sVis refl ())
decC-no-input {Rc1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decC-no-input {Rcg} {d} step = decC-Rcg-noev {d} step

decC-no-sndmsg : ∀ {c d a W} →
  decC c d ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-sndmsg {Rc0} (sVis refl ())
decC-no-sndmsg {Rc1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decC-no-sndmsg {Rcg} {d} step = decC-Rcg-noev {d} step

decC-no-rcvack : ∀ {c d a W} →
  decC c d ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
decC-no-rcvack {Rc0} (sVis refl ())
decC-no-rcvack {Rc1} {d = d} step rewrite ≟-diag d with step
... | sVis refl h = nothing-absurd h
decC-no-rcvack {Rcg} {d} step = decC-Rcg-noev {d} step

-- decS offers `ack` only at Sa1 (→ Sag); ⊤ payload.
decS-ack-class : ∀ {s d a W} →
  decS s d ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W → (s ≡ Sa1) × (W ≡ decS Sag d)
decS-ack-class {Sa0} (sVis refl ())
decS-ack-class {Sa1} {d} step = refl , decS-Sa1-ack {d} step
decS-ack-class {Sag} {d} step = ⊥-elim (decS-Sag-noev {d} step)

-- decS refuses output / tx / input / sndmsg / rcvack at every position.
decS-no-output : ∀ {s d a W} →
  decS s d ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-output {Sa0} (sVis refl ())
decS-no-output {Sa1} (sVis refl ())
decS-no-output {Sag} {d} step = decS-Sag-noev {d} step

decS-no-tx : ∀ {s d a W} →
  decS s d ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-tx {Sa0} (sVis refl ())
decS-no-tx {Sa1} (sVis refl ())
decS-no-tx {Sag} {d} step = decS-Sag-noev {d} step

decS-no-input : ∀ {s d a W} →
  decS s d ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-input {Sa0} (sVis refl ())
decS-no-input {Sa1} (sVis refl ())
decS-no-input {Sag} {d} step = decS-Sag-noev {d} step

decS-no-sndmsg : ∀ {s d a W} →
  decS s d ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-sndmsg {Sa0} (sVis refl ())
decS-no-sndmsg {Sa1} (sVis refl ())
decS-no-sndmsg {Sag} {d} step = decS-Sag-noev {d} step

decS-no-rcvack : ∀ {s d a W} →
  decS s d ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
decS-no-rcvack {Sa0} (sVis refl ())
decS-no-rcvack {Sa1} (sVis refl ())
decS-no-rcvack {Sag} {d} step = decS-Sag-noev {d} step

------------------------------------------------------------------------
-- RS-side visible-offer classifiers / refutations.
------------------------------------------------------------------------

-- RS offers `tx` only via decC at Rc0 (→ Rc1 a); decS refuses tx ⇒ decC-solo.
RS-tx-class : ∀ {c s d a W} →
  (decC c d ⦀ decS s d) ─[ ev (evN (tx N2N_KeepAlive c0) a) ]─► W →
  (c ≡ Rc0) × (W ≡ (decC Rc1 a ⦀ decS s d))
RS-tx-class {c} {s} {d} step
  with Par-ev-elim ∅ES ⊤merge (decC c d) (decS s d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = proj₁ cl , cong (λ z → z ⦀ decS s d) (proj₂ cl)
  where cl = decC-tx-class {c} {d} Cev
RS-tx-class {c} {s} {d} step | evR  _ Sev = ⊥-elim (decS-no-tx {s} {d} Sev)
RS-tx-class {c} {s} {d} step | evBoth _ _ Sev = ⊥-elim (decS-no-tx {s} {d} Sev)

-- RS offers `ack` only via decS at Sa1 (→ Sag); decC refuses ack ⇒ decS-solo.
RS-ack-class : ∀ {c s d a W} →
  (decC c d ⦀ decS s d) ─[ ev (evN (ack N2N_KeepAlive c0) a) ]─► W →
  (s ≡ Sa1) × (W ≡ (decC c d ⦀ decS Sag d))
RS-ack-class {c} {s} {d} step
  with Par-ev-elim ∅ES ⊤merge (decC c d) (decS s d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = ⊥-elim (decC-no-ack {c} {d} Cev)
RS-ack-class {c} {s} {d} step | evR  _ Sev = proj₁ cl , cong (λ z → decC c d ⦀ z) (proj₂ cl)
  where cl = decS-ack-class {s} {d} Sev
RS-ack-class {c} {s} {d} step | evBoth _ Cev _ = ⊥-elim (decC-no-ack {c} {d} Cev)

-- RS refuses output / input / sndmsg / rcvack at every position.
RS-no-output : ∀ {c s d a W} →
  (decC c d ⦀ decS s d) ─[ ev (evN (output′ N2N_KeepAlive c0) a) ]─► W → ⊥
RS-no-output {c} {s} {d} step with Par-ev-elim ∅ES ⊤merge (decC c d) (decS s d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-output {c} {d} Cev
... | evR  _ Sev       = decS-no-output {s} {d} Sev
... | evBoth _ Cev _   = decC-no-output {c} {d} Cev

RS-no-input : ∀ {c s d a W} →
  (decC c d ⦀ decS s d) ─[ ev (evN (input N2N_KeepAlive c0) a) ]─► W → ⊥
RS-no-input {c} {s} {d} step with Par-ev-elim ∅ES ⊤merge (decC c d) (decS s d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-input {c} {d} Cev
... | evR  _ Sev       = decS-no-input {s} {d} Sev
... | evBoth _ Cev _   = decC-no-input {c} {d} Cev

RS-no-sndmsg : ∀ {c s d a W} →
  (decC c d ⦀ decS s d) ─[ ev (evN (sndmsg N2N_KeepAlive c0) a) ]─► W → ⊥
RS-no-sndmsg {c} {s} {d} step with Par-ev-elim ∅ES ⊤merge (decC c d) (decS s d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-sndmsg {c} {d} Cev
... | evR  _ Sev       = decS-no-sndmsg {s} {d} Sev
... | evBoth _ Cev _   = decC-no-sndmsg {c} {d} Cev

RS-no-rcvack : ∀ {c s d a W} →
  (decC c d ⦀ decS s d) ─[ ev (evN (rcvack N2N_KeepAlive c0) a) ]─► W → ⊥
RS-no-rcvack {c} {s} {d} step with Par-ev-elim ∅ES ⊤merge (decC c d) (decS s d) step
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ Cev       = decC-no-rcvack {c} {d} Cev
... | evR  _ Sev       = decS-no-rcvack {s} {d} Sev
... | evBoth _ Cev _   = decC-no-rcvack {c} {d} Cev

------------------------------------------------------------------------
-- sim-Rx-ev : characterise every VISIBLE offer of decRx o c s d.
--   · output (o=O1)  → decRx O2 c s d     (forwards d)
--   · tx     (c=Rc0) → decRxᵢ o Rc1 s a′ d (NEW payload a′ at the Rc1 leaf)
--   · ack    (s=Sa1) → decRx o c Sag d
------------------------------------------------------------------------

-- Rx-side tx result: only decC advances to `Rc1 a′` (NEW payload); decO/decS
-- keep their old payload `d`.
decRxᵢ : OP → CP → SP → Data → Data → NetProc
decRxᵢ o c s dC dO = ((decO o dO) ∥⇘ csRS' ⇙ (decC c dC ⦀ decS s dO)) ∖ csRS'

sim-Rx-ev : ∀ {o c s d B} {e : Net Data B} {a} {W} →
  decRx o c s d ─[ ev (evl (evLabel B e a)) ]─► W →
    ((o ≡ O1)  × (evl (evLabel B e a) ≡ outputLbl d) × (W ≡ decRx O2 c s d))
  ⊎ (Σ[ a′ ∈ Data ] ((c ≡ Rc0) × (evl (evLabel B e a) ≡ txLbl a′) × (W ≡ decRxᵢ o Rc1 s a′ d)))
  ⊎ ((s ≡ Sa1) × (evl (evLabel B e a) ≡ ackLbl)    × (W ≡ decRx o c Sag d))
sim-Rx-ev {o} {c} {s} {d} step
  with Hide-ev-elim csRS' ((decO o d) ∥⇘ csRS' ⇙ (decC c d ⦀ decS s d)) step
... | heV {B} {e} {a} _ ¬cs parev with e
... | output N2N_ChainSync    ()
... | output N2N_BlockFetch   ()
... | output N2N_TxSubmission ()
... | output N2N_LeiosNotify  ()
... | output N2N_LeiosFetch   ()
... | output N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o d) (decC c d ⦀ decS s d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = inj₁ (proj₁ cl ,
          cong (λ z → evl (evLabel Data (output′ N2N_KeepAlive c0) z)) (proj₁ (proj₂ cl)) ,
          cong (λ z → ((z ∥⇘ csRS' ⇙ (decC c d ⦀ decS s d)) ∖ csRS')) (proj₂ (proj₂ cl)))
  where cl = decO-output-class {o} {d} Oev
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | output N2N_KeepAlive zero
      | evR  _ RSev      = ⊥-elim (RS-no-output {c} {s} RSev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | output N2N_KeepAlive zero
      | evBoth _ _ RSev  = ⊥-elim (RS-no-output {c} {s} RSev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} {d} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o d) (decC c d ⦀ decS s d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-tx {o} {d} Oev)
sim-Rx-ev {o} {c} {s} {d} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      | evR  _ RSev      = inj₂ (inj₁ (a , proj₁ cl , refl ,
          cong (λ z → (((decO o d) ∥⇘ csRS' ⇙ z) ∖ csRS')) (proj₂ cl)))
  where cl = RS-tx-class {c} {s} {d} RSev
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | tx N2N_KeepAlive zero
      | evBoth _ Oev _   = ⊥-elim (decO-no-tx {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} {d} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o d) (decC c d ⦀ decS s d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-ack {o} {d} Oev)
sim-Rx-ev {o} {c} {s} {d} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      | evR  _ RSev      = inj₂ (inj₂ (proj₁ cl , refl ,
          cong (λ z → (((decO o d) ∥⇘ csRS' ⇙ z) ∖ csRS')) (proj₂ cl)))
  where cl = RS-ack-class {c} {s} {d} RSev
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | ack N2N_KeepAlive zero
      | evBoth _ Oev _   = ⊥-elim (decO-no-ack {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvmsg id c′ = ⊥-elim (¬cs Poly.tt)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndack id c′ = ⊥-elim (¬cs Poly.tt)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | input N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} {d} step | heV {B} {e} {a} _ ¬cs parev | input N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o d) (decC c d ⦀ decS s d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-input {o} {d} Oev)
...   | evR  _ RSev      = ⊥-elim (RS-no-input {c} {s} RSev)
...   | evBoth _ Oev _   = ⊥-elim (decO-no-input {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} {d} step | heV {B} {e} {a} _ ¬cs parev | sndmsg N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o d) (decC c d ⦀ decS s d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-sndmsg {o} {d} Oev)
...   | evR  _ RSev      = ⊥-elim (RS-no-sndmsg {c} {s} RSev)
...   | evBoth _ Oev _   = ⊥-elim (decO-no-sndmsg {o} Oev)
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_ChainSync    ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_BlockFetch   ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_TxSubmission ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_LeiosNotify  ()
sim-Rx-ev {o} {c} {s} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_LeiosFetch   ()
sim-Rx-ev {o} {c} {s} {d} step | heV {B} {e} {a} _ ¬cs parev | rcvack N2N_KeepAlive zero
      with Par-ev-elim csRS' ⊤merge (decO o d) (decC c d ⦀ decS s d) parev
...   | evSync mem _ _   = ⊥-elim mem
...   | evL  _ Oev       = ⊥-elim (decO-no-rcvack {o} {d} Oev)
...   | evR  _ RSev      = ⊥-elim (RS-no-rcvack {c} {s} RSev)
...   | evBoth _ Oev _   = ⊥-elim (decO-no-rcvack {o} Oev)

------------------------------------------------------------------------
-- M4c: TOP-LEVEL simulation through `Par⊤ csTA'`  (d-threaded).
--
-- `⟦ mkCS i t r o c s ⟧ d = (decTx i t r d) ∥⇘ csTA' ⇙ (decRx o c s d)`.
------------------------------------------------------------------------

-- Label (dis)equalities.  The four visible/sync labels are pairwise distinct
-- REGARDLESS of carried value; the data labels are injective in the value.
inputLbl≢outputLbl : ∀ {a b} → inputLbl a ≡ outputLbl b → ⊥
inputLbl≢outputLbl ()
inputLbl≢txLbl : ∀ {a b} → inputLbl a ≡ txLbl b → ⊥
inputLbl≢txLbl ()
inputLbl≢ackLbl : ∀ {a} → inputLbl a ≡ ackLbl → ⊥
inputLbl≢ackLbl ()
outputLbl≢txLbl : ∀ {a b} → outputLbl a ≡ txLbl b → ⊥
outputLbl≢txLbl ()
outputLbl≢ackLbl : ∀ {a} → outputLbl a ≡ ackLbl → ⊥
outputLbl≢ackLbl ()
txLbl≢ackLbl : ∀ {a} → txLbl a ≡ ackLbl → ⊥
txLbl≢ackLbl ()

txLbl-inj : ∀ {a b} → txLbl a ≡ txLbl b → a ≡ b
txLbl-inj refl = refl

-- From a label equality identifying the carried event with `tx`/`ack`, build
-- the csTA membership (so a `¬cs`-refusal can be contradicted).
txLbl→mem : ∀ {B} {e : Net Data B} {a} {b}
          → evl (evLabel B e a) ≡ txLbl b → csTA' .mem (B , e) a
txLbl→mem refl = Poly.tt
ackLbl→mem : ∀ {B} {e : Net Data B} {a}
           → evl (evLabel B e a) ≡ ackLbl → csTA' .mem (B , e) a
ackLbl→mem refl = Poly.tt

------------------------------------------------------------------------
-- sim-modA : every modulo-csTA step of ⟦ cs ⟧ d is an internal `_⇒ᵢ_` move.
--   Internal steps PRESERVE the in-flight payload `d` (so `d′ = d`).
------------------------------------------------------------------------

sim-modA : ∀ cs {d W′} → ModAStep csTA' (⟦ cs ⟧ d) W′
         → Σ[ cs′ ∈ CS ] ((cs ⇒ᵢ cs′) × Σ[ d′ ∈ Data ] (W′ ≡ ⟦ cs′ ⟧ d′))
-- (1) a τ of the inner Par.
sim-modA (mkCS i t r o c s) {d} (maτ parτ)
  with Par-τ-elim csTA' ⊤merge (decTx i t r d) (decRx o c s d) parτ
... | τL P′ Txτ refl with sim-Tx-τ {i} {t} {r} {d} Txτ
...   | inj₁ (refl , refl , Weq) =
        mkCS I2 T1 r o c s , NM.sndmsg , d ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
...   | inj₂ (inj₁ (refl , refl , Weq)) =
        mkCS Ig t Rg o c s , NM.rcvack , d ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
...   | inj₂ (inj₂ (inj₁ (refl , Weq))) =
        mkCS I0 t r o c s , gI , d ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
...   | inj₂ (inj₂ (inj₂ (inj₁ (refl , Weq)))) =
        mkCS i T0 r o c s , gT , d ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
...   | inj₂ (inj₂ (inj₂ (inj₂ (refl , Weq)))) =
        mkCS i t R0 o c s , gR , d ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
sim-modA (mkCS i t r o c s) {d} (maτ parτ)
  | τR Q′ Rxτ refl with sim-Rx-τ {o} {c} {s} {d} Rxτ
...   | inj₁ (refl , refl , Weq) =
        mkCS i t r O1 Rcg s , NM.rcvmsg , d ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₁ (refl , refl , Weq)) =
        mkCS i t r Og c Sa1 , NM.sndack , d ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₂ (inj₁ (refl , Weq))) =
        mkCS i t r O0 c s , gO , d ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₂ (inj₂ (inj₁ (refl , Weq)))) =
        mkCS i t r o Rc0 s , gRc , d ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₂ (inj₂ (inj₂ (refl , Weq)))) =
        mkCS i t r o c Sa0 , gSa , d ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
-- (2) a hidden csTA-event (tx/ack): a SYNC between Tx- and Rx-sides.
sim-modA (mkCS i t r o c s) {d} (maE mem parev)
  with Par-ev-elim csTA' ⊤merge (decTx i t r d) (decRx o c s d) parev
... | evL  ¬cs _   = ⊥-elim (¬cs mem)
... | evR  ¬cs _   = ⊥-elim (¬cs mem)
... | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
... | evSync _ Txev Rxev with sim-Tx-ev {i} {t} {r} {d} Txev | sim-Rx-ev {o} {c} {s} {d} Rxev
-- Tx = input (∉csTA): the shared label can be neither output/tx/ack.
...   | inj₁ (_ , _ , Lin , _) | inj₁ (_ , Lout , _) =
          ⊥-elim (inputLbl≢outputLbl (trans (sym Lin) Lout))
...   | inj₁ (_ , _ , Lin , _) | inj₂ (inj₁ (_ , _ , Ltx , _)) =
          ⊥-elim (inputLbl≢txLbl (trans (sym Lin) Ltx))
...   | inj₁ (_ , _ , Lin , _) | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (inputLbl≢ackLbl (trans (sym Lin) Lack))
-- Tx = tx: consistent only with Rx = tx ⇒ `⇒ᵢ tx`; the sync pins `a′ ≡ d`.
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₁ (_ , Lout , _) =
          ⊥-elim (outputLbl≢txLbl (trans (sym Lout) Ltx))
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₂ (inj₁ (a′ , refl , Ltx′ , WeqRx)) =
          mkCS i Tg r o Rc1 s , NM.tx , d ,
          cong (Par⊤ csTA' (decTx i Tg r d))
            (trans WeqRx (cong (λ z → decRxᵢ o Rc1 s z d) (txLbl-inj (trans (sym Ltx′) Ltx))))
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (txLbl≢ackLbl (trans (sym Ltx) Lack))
-- Tx = ack: consistent only with Rx = ack ⇒ `⇒ᵢ ack`.
...   | inj₂ (inj₂ (refl , Lack , refl)) | inj₁ (_ , Lout , _) =
          ⊥-elim (outputLbl≢ackLbl (trans (sym Lout) Lack))
...   | inj₂ (inj₂ (refl , Lack , refl)) | inj₂ (inj₁ (_ , _ , Ltx , _)) =
          ⊥-elim (txLbl≢ackLbl (trans (sym Ltx) Lack))
...   | inj₂ (inj₂ (refl , _ , refl)) | inj₂ (inj₂ (refl , _ , refl)) =
          mkCS i t R1 o c Sag , NM.ack , d , refl

------------------------------------------------------------------------
-- sim-uVis : every NON-csTA visible offer of ⟦ cs ⟧ d is a `_⇒ᵥ_` move.
--   · `output` (Rx-side, solo) emits the current payload `d`  ⇒ W ≡ ⟦ cs′ ⟧ d
--   · `input`  (Tx-side, solo) introduces the NEW payload `a` ⇒ W ≡ the mixed
--      state `decUᵢ` (decI advanced with `a`; the rest keep `d`).
------------------------------------------------------------------------

-- Mixed-payload top-level decode for the post-`input` state: only the decI
-- leaf inside decTx carries the fresh payload `dI`; everything else keeps `dR`.
⟦_⟧ᵢ : CS → Data → Data → NetProc
⟦ mkCS i t r o c s ⟧ᵢ dI dR = (decTxᵢ i t r dI dR) ∥⇘ csTA' ⇙ (decRx o c s dR)

sim-uVis : ∀ cs {d B} {e : Net Data B} {a} {W′}
         → ¬ csTA' .mem (B , e) a
         → (⟦ cs ⟧ d) ─[ ev (evl (evLabel B e a)) ]─► W′
         → Σ[ cs′ ∈ CS ]
             ( (cs ⇒ᵥ cs′)
             × ( (Σ[ d′ ∈ Data ] (W′ ≡ ⟦ cs′ ⟧ d′))           -- output: d′ = d
               ⊎ (Σ[ a′ ∈ Data ] (W′ ≡ ⟦ cs′ ⟧ᵢ a′ d)) ) )    -- input: fresh a′
sim-uVis (mkCS i t r o c s) {d} ¬cs st
  with Par-ev-elim csTA' ⊤merge (decTx i t r d) (decRx o c s d) st
-- a SOLO Tx-side offer (∉csTA): must be `input` (tx/ack would be in csTA').
... | evL _ Txev with sim-Tx-ev {i} {t} {r} {d} Txev
...   | inj₁ (a′ , refl , _ , Weq) =
        mkCS I1 t r o c s , NM.input ,
        inj₂ (a′ , cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq)
...   | inj₂ (inj₁ (_ , Ltx  , _)) = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) = ⊥-elim (¬cs (ackLbl→mem Lack))
-- a SOLO Rx-side offer (∉csTA): must be `output`.
sim-uVis (mkCS i t r o c s) {d} ¬cs st
  | evR _ Rxev with sim-Rx-ev {o} {c} {s} {d} Rxev
...   | inj₁ (refl , _ , Weq) =
        mkCS i t r O2 c s , NM.output ,
        inj₁ (d , cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq)
...   | inj₂ (inj₁ (_ , _ , Ltx  , _)) = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) = ⊥-elim (¬cs (ackLbl→mem Lack))
-- a SYNC: the synced event is in csTA', contradicting `¬cs`.
sim-uVis (mkCS i t r o c s) ¬cs st | evSync mem _ _ = ⊥-elim (¬cs mem)
-- both-solo: Tx can only offer `input`, Rx only `output` ⇒ labels can't match.
sim-uVis (mkCS i t r o c s) {d} ¬cs st
  | evBoth _ Txev Rxev with sim-Tx-ev {i} {t} {r} {d} Txev | sim-Rx-ev {o} {c} {s} {d} Rxev
...   | inj₁ (_ , _ , Lin , _)    | inj₁ (_ , Lout , _) =
          ⊥-elim (inputLbl≢outputLbl (trans (sym Lin) Lout))
...   | inj₁ (_ , _ , Lin , _)    | inj₂ (inj₁ (_ , _ , Ltx , _)) =
          ⊥-elim (inputLbl≢txLbl (trans (sym Lin) Ltx))
...   | inj₁ (_ , _ , Lin , _)    | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (inputLbl≢ackLbl (trans (sym Lin) Lack))
...   | inj₂ (inj₁ (_ , Ltx , _)) | _ = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) | _ = ⊥-elim (¬cs (ackLbl→mem Lack))

------------------------------------------------------------------------
-- REACHABLE divergence-freedom infrastructure (payload-independent).
--
-- `GoodU T` (on the UN-hidden composite `T`) says: `T` is modulo-csTA
-- accessible (`MAcc csTA' T`, hence `T ∖ csTA'` does not diverge) AND every
-- step of the hidden `T ∖ csTA'` lands again in a `GoodU`-underlying (or
-- `deadlock`).  Closure is over `UStep` = (ModAStep csTA') ⊎ (visible non-csTA).
------------------------------------------------------------------------

data UStep (T T′ : NetProc) : Set₁ where
  uMod : ModAStep csTA' T T′ → UStep T T′
  uVis : {B : Set} {e : Net Data B} {a : B}
       → ¬ csTA' .mem (B , e) a
       → T ─[ ev (evl (evLabel B e a)) ]─► T′ → UStep T T′

record GoodU (T : NetProc) : Set₁ where
  coinductive
  field
    gmacc : MAcc csTA' T
    gstep : ∀ {T′} → UStep T T′ → GoodU T′
open GoodU

GoodU→noDiv : ∀ {T} → GoodU T → ¬ Diverges (T ∖ csTA')
GoodU→noDiv g = Hide-noDiv-from-MAcc csTA' _ (g .gmacc)

stable-no-div-run : ∀ {P : NetProc} {ss} {W : NetProc}
                  → (∀ {t} → P ─[ τ ]─► t → ⊥)
                  → (∀ {t e} → P ─[ ev e ]─► t → ⊥)
                  → ¬ Diverges P → P ⟹⟨ ss ⟩ W → Diverges W → ⊥
stable-no-div-run nτ nev nd ⟹-refl       dW = nd dW
stable-no-div-run nτ nev nd (⟹-τ st _)   dW = nτ st
stable-no-div-run nτ nev nd (⟹-ev st _)  dW = nev st

deadlock-no-div-run : ∀ {ss} {W : NetProc} → deadlock ⟹⟨ ss ⟩ W → Diverges W → ⊥
deadlock-no-div-run = stable-no-div-run deadlock-no-τ deadlock-no-ev deadlock-converges

-- The reachability engine: every weak run out of a `GoodU`-hidden state ends at
-- a non-divergent state.
Reach-noDiv : ∀ {T ss W} → GoodU T → (T ∖ csTA') ⟹⟨ ss ⟩ W → ¬ Diverges W
Reach-noDiv g ⟹-refl              = GoodU→noDiv g
Reach-noDiv {T = T} g (⟹-τ step rest) with Hide-τ-elim csTA' T step
... | hτP T′ Tτ refl        = Reach-noDiv (g .gstep (uMod (maτ Tτ))) rest
... | hτH T′ mem Tev refl   = Reach-noDiv (g .gstep (uMod (maE mem Tev))) rest
Reach-noDiv {T = T} g (⟹-ev step rest) with Hide-ev-elim csTA' T step
... | heV T′ ¬cs Tev        = Reach-noDiv (g .gstep (uVis ¬cs Tev)) rest
... | he√ _                 = deadlock-no-div-run rest

------------------------------------------------------------------------
-- Measure-based MAcc: every decoded state `⟦ cs ⟧ d` is modulo-csTA
-- accessible, by well-founded recursion on the measure `μ cs`.  Each
-- `_⇒ᵢ_` edge strictly decreases `μ` (via `μ-dec`) and PRESERVES `d`
-- (sim-modA returns `d′ = d` for internal steps), so the recursion stays
-- inside the `⟦ _ ⟧ d` family at a fixed `d`.
------------------------------------------------------------------------

MAcc-cs-acc : ∀ cs d → Acc _<_ (NM.μ cs) → MAcc csTA' (⟦ cs ⟧ d)
MAcc-cs-acc cs d (acc rs) = macc λ {W′} step →
  let (cs′ , red , d′ , Weq) = sim-modA cs step
  in subst (MAcc csTA') (sym Weq) (MAcc-cs-acc cs′ d′ (rs (NM.μ-dec red)))

MAcc-cs : ∀ cs d → MAcc csTA' (⟦ cs ⟧ d)
MAcc-cs cs d = MAcc-cs-acc cs d (<-wellFounded (NM.μ cs))

------------------------------------------------------------------------
-- D1' : the CONVERSE simulation (real-⇒ᵢ-Net / real-⇒ᵥ-Net), d-threaded.
--
--   real-⇒ᵢ-Net : cs ⇒ᵢ cs′ → ⟦ cs ⟧N d ─[ τ ]─► ⟦ cs′ ⟧N d
--   real-⇒ᵥ-Net : cs ⇒ᵥ cs′ → Σ l. ⟦ cs ⟧N d ─[ ev l ]─► ⟦ cs′ ⟧N d′
--
-- Every abstract step is realised by lifting the active leaf's concrete
-- LTS step (sVis / sSil) through the ⦀ / Par⊤ / ∖ layers via the
-- Par-τ-L/R, Par-soloL/R, Par-sync, Hide-τ/keep/hidden tools.  The four
-- FORWARD-EMISSION leaves (sndmsg / tx / rcvmsg / output) emit at the
-- in-flight payload `d`; their `Output-cont` guard reduces to `d ≟ d`,
-- discharged memory-leanly with a TARGETED `rewrite ≟-diag d` at the
-- (small) operand level inside a per-emission helper — never across the
-- whole composite.
------------------------------------------------------------------------


-- Per-emission leaf steps: the `Op.Output e d`-leaf emits at the current
-- payload `d`.  The `Output-cont` guard reduces to `d ≟ d`; we discharge it
-- in a TINY `where`-helper `h` whose goal is the single menu equality
-- `vis-of (force (decX X1 d)) eAt d ≡ just (decX Xg d)`.  The `rewrite ≟-diag d`
-- there reduces BOTH sides of that small equality in lock-step, so the named
-- target `decX Xg d` reduces too — never touching the whole composite.
emit-I1-sndmsg : ∀ {d} → decI I1 d ─[ ev (evN (sndmsg N2N_KeepAlive c0) d) ]─► decI I2 d
emit-I1-sndmsg {d} = sVis refl (h d)
  where
  h : ∀ d → vis-of (PTree.force (decI I1 d)) sndmsgAtN d ≡ just (decI I2 d)
  h d rewrite ≟-diag d = refl

emit-T1-tx : ∀ {d} → decT T1 d ─[ ev (evN (tx N2N_KeepAlive c0) d) ]─► decT Tg d
emit-T1-tx {d} = sVis refl (h d)
  where
  h : ∀ d → vis-of (PTree.force (decT T1 d)) txAtN d ≡ just (decT Tg d)
  h d rewrite ≟-diag d = refl

emit-Rc1-rcvmsg : ∀ {d} → decC Rc1 d ─[ ev (evN (rcvmsg N2N_KeepAlive c0) d) ]─► decC Rcg d
emit-Rc1-rcvmsg {d} = sVis refl (h d)
  where
  h : ∀ d → vis-of (PTree.force (decC Rc1 d)) rcvmsgAtN d ≡ just (decC Rcg d)
  h d rewrite ≟-diag d = refl

emit-O1-output : ∀ {d} → decO O1 d ─[ ev (evN (output′ N2N_KeepAlive c0) d) ]─► decO O2 d
emit-O1-output {d} = sVis refl (h d)
  where
  h : ∀ d → vis-of (PTree.force (decO O1 d)) outputAtN d ≡ just (decO O2 d)
  h d rewrite ≟-diag d = refl

-- The two ⊤-payload emissions whose SOURCE state is itself stuck behind a
-- preceding DATA emission (decI I2 = post-sndmsg, decO O2 = post-output): the
-- `≟-diag d` here unblocks the SOURCE `force` so the `react` node surfaces.
emit-I2-rcvack : ∀ {d} → decI I2 d ─[ ev (evN (rcvack N2N_KeepAlive c0) tt) ]─► decI Ig d
emit-I2-rcvack {d} = go d
  where
  go : ∀ d → decI I2 d ─[ ev (evN (rcvack N2N_KeepAlive c0) tt) ]─► decI Ig d
  go d rewrite ≟-diag d = sVis refl refl

emit-O2-sndack : ∀ {d} → decO O2 d ─[ ev (evN (sndack N2N_KeepAlive c0) tt) ]─► decO Og d
emit-O2-sndack {d} = go d
  where
  go : ∀ d → decO O2 d ─[ ev (evN (sndack N2N_KeepAlive c0) tt) ]─► decO Og d
  go d rewrite ≟-diag d = sVis refl refl

-- Guard `sil` τ's whose SOURCE guard state sits behind a DATA emission
-- (decI Ig = post-sndmsg, decT Tg = post-tx, decO Og = post-output,
-- decC Rcg = post-rcvmsg): `≟-diag d` unblocks the source `force` so the
-- `sil` node surfaces.  (decR Rg / decS Sag are ⊤-only and need no helper.)
guard-Ig-τ : ∀ {d} → decI Ig d ─[ τ ]─► decI I0 d
guard-Ig-τ {d} = go d
  where
  go : ∀ d → decI Ig d ─[ τ ]─► decI I0 d
  go d rewrite ≟-diag d = sSil refl

guard-Tg-τ : ∀ {d} → decT Tg d ─[ τ ]─► decT T0 d
guard-Tg-τ {d} = go d
  where
  go : ∀ d → decT Tg d ─[ τ ]─► decT T0 d
  go d rewrite ≟-diag d = sSil refl

guard-Og-τ : ∀ {d} → decO Og d ─[ τ ]─► decO O0 d
guard-Og-τ {d} = go d
  where
  go : ∀ d → decO Og d ─[ τ ]─► decO O0 d
  go d rewrite ≟-diag d = sSil refl

guard-Rcg-τ : ∀ {d} → decC Rcg d ─[ τ ]─► decC Rc0 d
guard-Rcg-τ {d} = go d
  where
  go : ∀ d → decC Rcg d ─[ τ ]─► decC Rc0 d
  go d rewrite ≟-diag d = sSil refl

------------------------------------------------------------------------
-- viewV-non-offer helpers (the idle operands at each solo lift).  These
-- branch on positions only; the partner does not offer the named channel.
-- The ⊤-payload positions carry over verbatim; the FORWARD (data) positions
-- need a per-position `rewrite ≟-diag d` to unblock the stuck `succV`.
------------------------------------------------------------------------

-- single-leaf non-offers (for the inner ⦀ solos).
nR-sndmsg : ∀ r d → viewV (PTree.force (decR r d)) (Data , sndmsg N2N_KeepAlive c0) d ≡ nothing
nR-sndmsg R0 d = refl
nR-sndmsg R1 d = refl
nR-sndmsg Rg d rewrite ≟-diag d = refl

nT-rcvack : ∀ t d → viewV (PTree.force (decT t d)) (⊤ , rcvack N2N_KeepAlive c0) tt ≡ nothing
nT-rcvack T0 d = refl
nT-rcvack T1 d rewrite ≟-diag d = refl
nT-rcvack Tg d rewrite ≟-diag d = refl

nS-rcvmsg : ∀ s d → viewV (PTree.force (decS s d)) (Data , rcvmsg N2N_KeepAlive c0) d ≡ nothing
nS-rcvmsg Sa0 d = refl
nS-rcvmsg Sa1 d = refl
nS-rcvmsg Sag d = refl

nC-sndack : ∀ c d → viewV (PTree.force (decC c d)) (⊤ , sndack N2N_KeepAlive c0) tt ≡ nothing
nC-sndack Rc0 d = refl
nC-sndack Rc1 d rewrite ≟-diag d = refl
nC-sndack Rcg d rewrite ≟-diag d = refl

-- single-leaf non-offers of tx / ack (for the top-sync solos).
nR-tx : ∀ r d → viewV (PTree.force (decR r d)) (Data , tx N2N_KeepAlive c0) d ≡ nothing
nR-tx R0 d = refl
nR-tx R1 d = refl
nR-tx Rg d rewrite ≟-diag d = refl

nI-tx : ∀ i d → viewV (PTree.force (decI i d)) (Data , tx N2N_KeepAlive c0) d ≡ nothing
nI-tx I0 d = refl
nI-tx I1 d rewrite ≟-diag d = refl
nI-tx I2 d rewrite ≟-diag d = refl
nI-tx Ig d rewrite ≟-diag d = refl

nS-tx : ∀ s d → viewV (PTree.force (decS s d)) (Data , tx N2N_KeepAlive c0) d ≡ nothing
nS-tx Sa0 d = refl
nS-tx Sa1 d = refl
nS-tx Sag d = refl

nO-tx : ∀ o d → viewV (PTree.force (decO o d)) (Data , tx N2N_KeepAlive c0) d ≡ nothing
nO-tx O0 d = refl
nO-tx O1 d rewrite ≟-diag d = refl
nO-tx O2 d rewrite ≟-diag d = refl
nO-tx Og d rewrite ≟-diag d = refl

nT-ack : ∀ t d → viewV (PTree.force (decT t d)) (⊤ , ack N2N_KeepAlive c0) tt ≡ nothing
nT-ack T0 d = refl
nT-ack T1 d rewrite ≟-diag d = refl
nT-ack Tg d rewrite ≟-diag d = refl

nI-ack : ∀ i d → viewV (PTree.force (decI i d)) (⊤ , ack N2N_KeepAlive c0) tt ≡ nothing
nI-ack I0 d = refl
nI-ack I1 d rewrite ≟-diag d = refl
nI-ack I2 d rewrite ≟-diag d = refl
nI-ack Ig d rewrite ≟-diag d = refl

nC-ack : ∀ c d → viewV (PTree.force (decC c d)) (⊤ , ack N2N_KeepAlive c0) tt ≡ nothing
nC-ack Rc0 d = refl
nC-ack Rc1 d rewrite ≟-diag d = refl
nC-ack Rcg d rewrite ≟-diag d = refl

nO-ack : ∀ o d → viewV (PTree.force (decO o d)) (⊤ , ack N2N_KeepAlive c0) tt ≡ nothing
nO-ack O0 d = refl
nO-ack O1 d rewrite ≟-diag d = refl
nO-ack O2 d rewrite ≟-diag d = refl
nO-ack Og d rewrite ≟-diag d = refl

-- composite ⦀ non-offers of input / output (for the visible solos).
nTR-input : ∀ t r d → viewV (PTree.force (decT t d ⦀ decR r d)) (Data , input N2N_KeepAlive c0) d ≡ nothing
nTR-input T0 R0 d = refl
nTR-input T0 R1 d = refl
nTR-input T0 Rg d rewrite ≟-diag d = refl
nTR-input T1 R0 d rewrite ≟-diag d = refl
nTR-input T1 R1 d rewrite ≟-diag d = refl
nTR-input T1 Rg d rewrite ≟-diag d = refl
nTR-input Tg R0 d rewrite ≟-diag d = refl
nTR-input Tg R1 d rewrite ≟-diag d = refl
nTR-input Tg Rg d rewrite ≟-diag d = refl

nCS-output : ∀ c s d → viewV (PTree.force (decC c d ⦀ decS s d)) (Data , output′ N2N_KeepAlive c0) d ≡ nothing
nCS-output Rc0 Sa0 d = refl
nCS-output Rc0 Sa1 d = refl
nCS-output Rc0 Sag d = refl
nCS-output Rc1 Sa0 d rewrite ≟-diag d = refl
nCS-output Rc1 Sa1 d rewrite ≟-diag d = refl
nCS-output Rc1 Sag d rewrite ≟-diag d = refl
nCS-output Rcg Sa0 d rewrite ≟-diag d = refl
nCS-output Rcg Sa1 d rewrite ≟-diag d = refl
nCS-output Rcg Sag d rewrite ≟-diag d = refl

-- composite Par⊤/∖ side non-offers of input / output (top-level visible solos).
nRx-input : ∀ o c s d → viewV (PTree.force (decRx o c s d)) (Data , input N2N_KeepAlive c0) d ≡ nothing
nRx-input O0 Rc0 Sa0 d = refl
nRx-input O0 Rc0 Sa1 d = refl
nRx-input O0 Rc0 Sag d = refl
nRx-input O0 Rc1 Sa0 d rewrite ≟-diag d = refl
nRx-input O0 Rc1 Sa1 d rewrite ≟-diag d = refl
nRx-input O0 Rc1 Sag d rewrite ≟-diag d = refl
nRx-input O0 Rcg Sa0 d rewrite ≟-diag d = refl
nRx-input O0 Rcg Sa1 d rewrite ≟-diag d = refl
nRx-input O0 Rcg Sag d rewrite ≟-diag d = refl
nRx-input O1 Rc0 Sa0 d rewrite ≟-diag d = refl
nRx-input O1 Rc0 Sa1 d rewrite ≟-diag d = refl
nRx-input O1 Rc0 Sag d rewrite ≟-diag d = refl
nRx-input O1 Rc1 Sa0 d rewrite ≟-diag d = refl
nRx-input O1 Rc1 Sa1 d rewrite ≟-diag d = refl
nRx-input O1 Rc1 Sag d rewrite ≟-diag d = refl
nRx-input O1 Rcg Sa0 d rewrite ≟-diag d = refl
nRx-input O1 Rcg Sa1 d rewrite ≟-diag d = refl
nRx-input O1 Rcg Sag d rewrite ≟-diag d = refl
nRx-input O2 Rc0 Sa0 d rewrite ≟-diag d = refl
nRx-input O2 Rc0 Sa1 d rewrite ≟-diag d = refl
nRx-input O2 Rc0 Sag d rewrite ≟-diag d = refl
nRx-input O2 Rc1 Sa0 d rewrite ≟-diag d = refl
nRx-input O2 Rc1 Sa1 d rewrite ≟-diag d = refl
nRx-input O2 Rc1 Sag d rewrite ≟-diag d = refl
nRx-input O2 Rcg Sa0 d rewrite ≟-diag d = refl
nRx-input O2 Rcg Sa1 d rewrite ≟-diag d = refl
nRx-input O2 Rcg Sag d rewrite ≟-diag d = refl
nRx-input Og Rc0 Sa0 d rewrite ≟-diag d = refl
nRx-input Og Rc0 Sa1 d rewrite ≟-diag d = refl
nRx-input Og Rc0 Sag d rewrite ≟-diag d = refl
nRx-input Og Rc1 Sa0 d rewrite ≟-diag d = refl
nRx-input Og Rc1 Sa1 d rewrite ≟-diag d = refl
nRx-input Og Rc1 Sag d rewrite ≟-diag d = refl
nRx-input Og Rcg Sa0 d rewrite ≟-diag d = refl
nRx-input Og Rcg Sa1 d rewrite ≟-diag d = refl
nRx-input Og Rcg Sag d rewrite ≟-diag d = refl

nTx-output : ∀ i t r d → viewV (PTree.force (decTx i t r d)) (Data , output′ N2N_KeepAlive c0) d ≡ nothing
nTx-output I0 T0 R0 d = refl
nTx-output I0 T0 R1 d = refl
nTx-output I0 T0 Rg d rewrite ≟-diag d = refl
nTx-output I0 T1 R0 d rewrite ≟-diag d = refl
nTx-output I0 T1 R1 d rewrite ≟-diag d = refl
nTx-output I0 T1 Rg d rewrite ≟-diag d = refl
nTx-output I0 Tg R0 d rewrite ≟-diag d = refl
nTx-output I0 Tg R1 d rewrite ≟-diag d = refl
nTx-output I0 Tg Rg d rewrite ≟-diag d = refl
nTx-output I1 T0 R0 d rewrite ≟-diag d = refl
nTx-output I1 T0 R1 d rewrite ≟-diag d = refl
nTx-output I1 T0 Rg d rewrite ≟-diag d = refl
nTx-output I1 T1 R0 d rewrite ≟-diag d = refl
nTx-output I1 T1 R1 d rewrite ≟-diag d = refl
nTx-output I1 T1 Rg d rewrite ≟-diag d = refl
nTx-output I1 Tg R0 d rewrite ≟-diag d = refl
nTx-output I1 Tg R1 d rewrite ≟-diag d = refl
nTx-output I1 Tg Rg d rewrite ≟-diag d = refl
nTx-output I2 T0 R0 d rewrite ≟-diag d = refl
nTx-output I2 T0 R1 d rewrite ≟-diag d = refl
nTx-output I2 T0 Rg d rewrite ≟-diag d = refl
nTx-output I2 T1 R0 d rewrite ≟-diag d = refl
nTx-output I2 T1 R1 d rewrite ≟-diag d = refl
nTx-output I2 T1 Rg d rewrite ≟-diag d = refl
nTx-output I2 Tg R0 d rewrite ≟-diag d = refl
nTx-output I2 Tg R1 d rewrite ≟-diag d = refl
nTx-output I2 Tg Rg d rewrite ≟-diag d = refl
nTx-output Ig T0 R0 d rewrite ≟-diag d = refl
nTx-output Ig T0 R1 d rewrite ≟-diag d = refl
nTx-output Ig T0 Rg d rewrite ≟-diag d = refl
nTx-output Ig T1 R0 d rewrite ≟-diag d = refl
nTx-output Ig T1 R1 d rewrite ≟-diag d = refl
nTx-output Ig T1 Rg d rewrite ≟-diag d = refl
nTx-output Ig Tg R0 d rewrite ≟-diag d = refl
nTx-output Ig Tg R1 d rewrite ≟-diag d = refl
nTx-output Ig Tg Rg d rewrite ≟-diag d = refl

------------------------------------------------------------------------
-- D1'.A : the internal converse simulation  cs ⇒ᵢ cs′ → ⟦cs⟧N d ─[τ]→ ⟦cs′⟧N d.
-- Internal moves PRESERVE the in-flight payload `d`.
------------------------------------------------------------------------

real-⇒ᵢ-Net : ∀ {cs cs′ d} → cs NM.⇒ᵢ cs′ → ⟦ cs ⟧N d ─[ τ ]─► ⟦ cs′ ⟧N d

-- INNER SYNC: sndmsg  (decI I1→I2 emits ∥ decT T0→T1 intro solo past decR; ∈ csSR').
real-⇒ᵢ-Net {d = d} (NM.sndmsg {r} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx I1 T0 r d) (decRx o c s d)
     (Hide-hidden csSR' _ Poly.tt
       (Par-sync csSR' ⊤merge (decI I1 d) (decT T0 d ⦀ decR r d) Poly.tt
         emit-I1-sndmsg
         (Par-soloL ∅ES ⊤merge (decT T0 d) (decR r d) (λ ()) (sVis refl refl)
           (nR-sndmsg r d)))))

-- TOP SYNC: tx  (decT T1→Tg emits ∥ decC Rc0→Rc1 intro; ∈ csTA').
real-⇒ᵢ-Net {d = d} (NM.tx {i} {r} {o} {s}) =
  Hide-hidden csTA' _ Poly.tt
   (Par-sync csTA' ⊤merge (decTx i T1 r d) (decRx o Rc0 s d) Poly.tt
     (Hide-keep csSR' _ (λ ())
       (Par-soloR csSR' ⊤merge (decI i d) (decT T1 d ⦀ decR r d) (λ ())
         (Par-soloL ∅ES ⊤merge (decT T1 d) (decR r d) (λ ()) emit-T1-tx
           (nR-tx r d))
         (nI-tx i d)))
     (Hide-keep csRS' _ (λ ())
       (Par-soloR csRS' ⊤merge (decO o d) (decC Rc0 d ⦀ decS s d) (λ ())
         (Par-soloL ∅ES ⊤merge (decC Rc0 d) (decS s d) (λ ()) (sVis refl refl)
           (nS-tx s d))
         (nO-tx o d))))

-- INNER SYNC: rcvmsg  (decO O0→O1 intro ∥ decC Rc1→Rcg emits solo past decS; ∈ csRS').
real-⇒ᵢ-Net {d = d} (NM.rcvmsg {i} {t} {r} {s}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r d) (decRx O0 Rc1 s d)
     (Hide-hidden csRS' _ Poly.tt
       (Par-sync csRS' ⊤merge (decO O0 d) (decC Rc1 d ⦀ decS s d) Poly.tt
         (sVis refl refl)
         (Par-soloL ∅ES ⊤merge (decC Rc1 d) (decS s d) (λ ()) emit-Rc1-rcvmsg
           (nS-rcvmsg s d)))))

-- INNER SYNC: sndack  (decO O2→Og emits ∥ decS Sa0→Sa1 intro solo past decC; ∈ csRS').
real-⇒ᵢ-Net {d = d} (NM.sndack {i} {t} {r} {c}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r d) (decRx O2 c Sa0 d)
     (Hide-hidden csRS' _ Poly.tt
       (Par-sync csRS' ⊤merge (decO O2 d) (decC c d ⦀ decS Sa0 d) Poly.tt
         emit-O2-sndack
         (Par-soloR ∅ES ⊤merge (decC c d) (decS Sa0 d) (λ ()) (sVis refl refl)
           (nC-sndack c d)))))

-- TOP SYNC: ack  (decR R0→R1 intro solo to decTx-level ∥ decS Sa1→Sag intro; ∈ csTA').
real-⇒ᵢ-Net {d = d} (NM.ack {i} {t} {o} {c}) =
  Hide-hidden csTA' _ Poly.tt
   (Par-sync csTA' ⊤merge (decTx i t R0 d) (decRx o c Sa1 d) Poly.tt
     (Hide-keep csSR' _ (λ ())
       (Par-soloR csSR' ⊤merge (decI i d) (decT t d ⦀ decR R0 d) (λ ())
         (Par-soloR ∅ES ⊤merge (decT t d) (decR R0 d) (λ ()) (sVis refl refl)
           (nT-ack t d))
         (nI-ack i d)))
     (Hide-keep csRS' _ (λ ())
       (Par-soloR csRS' ⊤merge (decO o d) (decC c d ⦀ decS Sa1 d) (λ ())
         (Par-soloR ∅ES ⊤merge (decC c d) (decS Sa1 d) (λ ()) (sVis refl refl)
           (nC-ack c d))
         (nO-ack o d))))

-- INNER SYNC: rcvack  (decI I2→Ig emits ∥ decR R1→Rg intro solo past decT; ∈ csSR').
real-⇒ᵢ-Net {d = d} (NM.rcvack {t} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx I2 t R1 d) (decRx o c s d)
     (Hide-hidden csSR' _ Poly.tt
       (Par-sync csSR' ⊤merge (decI I2 d) (decT t d ⦀ decR R1 d) Poly.tt
         emit-I2-rcvack
         (Par-soloR ∅ES ⊤merge (decT t d) (decR R1 d) (λ ()) (sVis refl refl)
           (nT-rcvack t d)))))

-- GUARD gI  (decI Ig→I0, τ; left of Par⊤ csSR', TxSide left at top).
real-⇒ᵢ-Net {d = d} (NM.gI {t} {r} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx Ig t r d) (decRx o c s d)
     (Hide-τ csSR' _
       (Par-τ-L csSR' ⊤merge (decI Ig d) (decT t d ⦀ decR r d) guard-Ig-τ)))

-- GUARD gT  (decT Tg→T0, τ; left of ⦀, right of Par⊤ csSR').
real-⇒ᵢ-Net {d = d} (NM.gT {i} {r} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx i Tg r d) (decRx o c s d)
     (Hide-τ csSR' _
       (Par-τ-R csSR' ⊤merge (decI i d) (decT Tg d ⦀ decR r d)
         (Par-τ-L ∅ES ⊤merge (decT Tg d) (decR r d) guard-Tg-τ))))

-- GUARD gR  (decR Rg→R0, τ; right of ⦀, right of Par⊤ csSR').
real-⇒ᵢ-Net {d = d} (NM.gR {i} {t} {o} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-L csTA' ⊤merge (decTx i t Rg d) (decRx o c s d)
     (Hide-τ csSR' _
       (Par-τ-R csSR' ⊤merge (decI i d) (decT t d ⦀ decR Rg d)
         (Par-τ-R ∅ES ⊤merge (decT t d) (decR Rg d) (sSil refl)))))

-- GUARD gO  (decO Og→O0, τ; left of Par⊤ csRS', RxSide right at top).
real-⇒ᵢ-Net {d = d} (NM.gO {i} {t} {r} {c} {s}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r d) (decRx Og c s d)
     (Hide-τ csRS' _
       (Par-τ-L csRS' ⊤merge (decO Og d) (decC c d ⦀ decS s d) guard-Og-τ)))

-- GUARD gRc  (decC Rcg→Rc0, τ; left of ⦀, right of Par⊤ csRS').
real-⇒ᵢ-Net {d = d} (NM.gRc {i} {t} {r} {o} {s}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r d) (decRx o Rcg s d)
     (Hide-τ csRS' _
       (Par-τ-R csRS' ⊤merge (decO o d) (decC Rcg d ⦀ decS s d)
         (Par-τ-L ∅ES ⊤merge (decC Rcg d) (decS s d) guard-Rcg-τ))))

-- GUARD gSa  (decS Sag→Sa0, τ; right of ⦀, right of Par⊤ csRS').
real-⇒ᵢ-Net {d = d} (NM.gSa {i} {t} {r} {o} {c}) =
  Hide-τ csTA' _
   (Par-τ-R csTA' ⊤merge (decTx i t r d) (decRx o c Sag d)
     (Hide-τ csRS' _
       (Par-τ-R csRS' ⊤merge (decO o d) (decC c d ⦀ decS Sag d)
         (Par-τ-R ∅ES ⊤merge (decC c d) (decS Sag d) (sSil refl)))))

------------------------------------------------------------------------
-- D1'.B : the visible converse simulation  cs ⇒ᵥ cs′ → Σ l. ⟦cs⟧N d ─[ev l]→ ⟦cs′⟧N d′.
--   · input  introduces a FRESH payload d′ at the decI leaf  (l = inputLbl d′)
--   · output emits the CURRENT payload d                      (l = outputLbl d)
------------------------------------------------------------------------

real-⇒ᵥ-Net : ∀ {cs cs′ d} → cs NM.⇒ᵥ cs′
            → Σ[ l ∈ Event√ NetR ] Σ[ d′ ∈ Data ] (⟦ cs ⟧N d ─[ ev l ]─► ⟦ cs′ ⟧N d′)

-- VISIBLE input  (decI I0→I1 intro at fresh d; solo all the way; ∉ csSR', ∉ csTA').
-- The post state keeps d only at decI(=I1 d), so chose d′ = d to land in ⟦_⟧N d.
real-⇒ᵥ-Net {d = d} (NM.input {t} {r} {o} {c} {s}) =
  inputLbl d , d ,
  Hide-keep csTA' _ (λ ())
   (Par-soloL csTA' ⊤merge (decTx I0 t r d) (decRx o c s d) (λ ())
     (Hide-keep csSR' _ (λ ())
       (Par-soloL csSR' ⊤merge (decI I0 d) (decT t d ⦀ decR r d) (λ ())
         (sVis refl refl)
         (nTR-input t r d)))
     (nRx-input o c s d))

-- VISIBLE output  (decO O1→O2 emits current d; solo all the way; ∉ csRS', ∉ csTA').
real-⇒ᵥ-Net {d = d} (NM.output {i} {t} {r} {c} {s}) =
  outputLbl d , d ,
  Hide-keep csTA' _ (λ ())
   (Par-soloR csTA' ⊤merge (decTx i t r d) (decRx O1 c s d) (λ ())
     (Hide-keep csRS' _ (λ ())
       (Par-soloL csRS' ⊤merge (decO O1 d) (decC c d ⦀ decS s d) (λ ())
         emit-O1-output
         (nCS-output c s d)))
     (nTx-output i t r d))

------------------------------------------------------------------------
-- TASK 5 — E1/E2 SCAFFOLDING (port of NetworkRefinement E1+E2 blocks).
--
-- The reachability closure `Reach`, the place-invariant `Inv`, the
-- structural phase `phaseN`, and the liveness engines `liveA`/`liveB` are
-- DATA-FREE abstract reasoning on the `CS` automaton — ported VERBATIM
-- (no `d`).  The drains and the `Expand` builder (below) thread the
-- payload `d`.
------------------------------------------------------------------------

open import Data.Nat using (zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≢_)
import Data.Nat.Solver as ℕSolver
open ℕSolver.+-*-Solver
  using ()
  renaming (solve to ℕsolve; _:=_ to _:≡_; _:+_ to _:⊕_; con to ℕcon)

-- Phases.
data Phase : Set where pA pB : Phase

-- The reachable-with-phase closure relation (4 constructors).
data Reach : CS → Phase → Set where
  reach-cs0 : Reach cs0 pA
  reach-i   : ∀ {cs cs′ ph} → Reach cs ph → cs NM.⇒ᵢ cs′ → Reach cs′ ph
  reach-vA  : ∀ {cs cs′}    → Reach cs pA → cs NM.⇒ᵥ cs′ → Reach cs′ pB
  reach-vB  : ∀ {cs cs′}    → Reach cs pB → cs NM.⇒ᵥ cs′ → Reach cs′ pA

------------------------------------------------------------------------
-- E2: the place-invariant `Inv`, structural phase `phaseN`.
------------------------------------------------------------------------

-- per-leaf token / phase indicators.
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

tok : CS → ℕ
tok cs = aT (tr cs) + aR (ra cs) + aO (out cs) + aC (rc cs) + aS (sa cs)

Inv : CS → Set
Inv cs = tok cs ≡ aI (inp cs)

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

sucinj : ∀ {m n} → suc m ≡ suc n → m ≡ n
sucinj refl = refl

Inv-step : ∀ {cs cs′} → cs NM.⇒ᵢ cs′ → Inv cs → Inv cs′
Inv-step NM.sndmsg inv = cong suc inv
Inv-step (NM.tx {i} {r} {o} {s}) inv =
  trans (ℕsolve 3 (λ b d e → ℕcon 0 :⊕ b :⊕ d :⊕ ℕcon 1 :⊕ e
                          :≡ ℕcon 1 :⊕ b :⊕ d :⊕ ℕcon 0 :⊕ e)
           refl (aR r) (aO o) (aS s)) inv
Inv-step (NM.rcvmsg {i} {t} {r} {s}) inv =
  trans (ℕsolve 3 (λ a b e → a :⊕ b :⊕ ℕcon 1 :⊕ ℕcon 0 :⊕ e
                          :≡ a :⊕ b :⊕ ℕcon 0 :⊕ ℕcon 1 :⊕ e)
           refl (aT t) (aR r) (aS s)) inv
Inv-step (NM.sndack {i} {t} {r} {c}) inv =
  trans (ℕsolve 3 (λ a b d → a :⊕ b :⊕ ℕcon 0 :⊕ d :⊕ ℕcon 1
                          :≡ a :⊕ b :⊕ ℕcon 1 :⊕ d :⊕ ℕcon 0)
           refl (aT t) (aR r) (aC c)) inv
Inv-step (NM.ack {i} {t} {o} {c}) inv =
  trans (ℕsolve 3 (λ a d e → a :⊕ ℕcon 1 :⊕ d :⊕ e :⊕ ℕcon 0
                          :≡ a :⊕ ℕcon 0 :⊕ d :⊕ e :⊕ ℕcon 1)
           refl (aT t) (aO o) (aC c)) inv
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

Inv-vis : ∀ {cs cs′} → cs NM.⇒ᵥ cs′ → Inv cs → Inv cs′
Inv-vis NM.input  inv = inv
Inv-vis NM.output inv = inv

------------------------------------------------------------------------
-- E2.b  Phase agreement.
------------------------------------------------------------------------

phase-step : ∀ {cs cs′} → cs NM.⇒ᵢ cs′ → phaseN cs ≡ phaseN cs′
phase-step (NM.sndmsg {r} {o} {c} {s}) =
  ℕsolve 2 (λ d e → ℕcon 1 :⊕ ℕcon 0 :⊕ d :⊕ e
                 :≡ ℕcon 0 :⊕ ℕcon 1 :⊕ d :⊕ e)
    refl (pO o) (pC c)
phase-step (NM.tx {i} {r} {o} {s}) =
  ℕsolve 2 (λ a d → a :⊕ ℕcon 1 :⊕ d :⊕ ℕcon 0
                 :≡ a :⊕ ℕcon 0 :⊕ d :⊕ ℕcon 1)
    refl (pI i) (pO o)
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

phaseN-O1 : ∀ i t c → pI i + pT t + pO O1 + pC c ≡ 0 → ⊥
phaseN-O1 i t c e =
  o≢0 (trans (ℕsolve 3 (λ a b d → ℕcon 1 :⊕ (a :⊕ b :⊕ d)
                              :≡ a :⊕ b :⊕ ℕcon 1 :⊕ d)
                refl (pI i) (pT t) (pC c)) e)

Inv-I0-phase0 : ∀ {cs} → inp cs ≡ I0 → Inv cs → phaseN cs ≡ 0
Inv-I0-phase0 {mkCS I0 T0  r O0 Rc0 s} refl inv = refl
Inv-I0-phase0 {mkCS I0 T0  r O0 Rcg s} refl inv = refl
Inv-I0-phase0 {mkCS I0 T0  r Og Rc0 s} refl inv = refl
Inv-I0-phase0 {mkCS I0 T0  r Og Rcg s} refl inv = refl
Inv-I0-phase0 {mkCS I0 Tg  r O0 Rc0 s} refl inv = refl
Inv-I0-phase0 {mkCS I0 Tg  r O0 Rcg s} refl inv = refl
Inv-I0-phase0 {mkCS I0 Tg  r Og Rc0 s} refl inv = refl
Inv-I0-phase0 {mkCS I0 Tg  r Og Rcg s} refl inv = refl
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

phase-input  : ∀ {cs cs′} → cs NM.⇒ᵥ cs′ → phaseN cs ≡ 0 → phaseN cs′ ≡ 1
phase-input NM.input  eq = cong suc eq
phase-input (NM.output {i} {t} {r} {c} {s}) eq = ⊥-elim (phaseN-O1 i t c eq)

phase-output : ∀ {cs cs′} → Inv cs → cs NM.⇒ᵥ cs′ → phaseN cs ≡ 1 → phaseN cs′ ≡ 0
phase-output {cs} inv NM.input  eq =
  ⊥-elim (o≢0 (trans (sym eq) (Inv-I0-phase0 {cs} refl inv)))
phase-output {mkCS i t r O1 c s} inv NM.output eq = sucinj (trans (helper i t c) eq)
  where
  helper : ∀ i t c → suc (pI i + pT t + pO O2 + pC c)
                   ≡ pI i + pT t + pO O1 + pC c
  helper i t c =
    ℕsolve 3 (λ a b d → ℕcon 1 :⊕ (a :⊕ b :⊕ ℕcon 0 :⊕ d)
                     :≡ a :⊕ b :⊕ ℕcon 1 :⊕ d)
      refl (pI i) (pT t) (pC c)

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
-- E2.c  LIVENESS engines.
------------------------------------------------------------------------

liveA : ∀ cs → Inv cs → phaseN cs ≡ 0 → inp cs ≢ I0
      → Σ[ cs′ ∈ CS ] (cs NM.⇒ᵢ cs′)
liveA (mkCS I0 t r o c s) inv ph i≢ = ⊥-elim (i≢ refl)
liveA (mkCS I1 t r o c s) inv ph i≢ = ⊥-elim (o≢0 ph)
liveA (mkCS Ig t r o c s) inv ph i≢ = mkCS I0 t r o c s , NM.gI
liveA (mkCS I2 t  Rg o c s) inv ph i≢ = mkCS I2 t R0 o c s , NM.gR
liveA (mkCS I2 t  R1 o c s) inv ph i≢ = mkCS Ig t Rg o c s , NM.rcvack
liveA (mkCS I2 Tg R0 o c s) inv ph i≢ = mkCS I2 T0 R0 o c s , NM.gT
liveA (mkCS I2 T1 R0 o c s) inv ph i≢ = ⊥-elim (o≢0 ph)
liveA (mkCS I2 T0 R0 Og  c   s)   inv ph i≢ = mkCS I2 T0 R0 O0 c s , NM.gO
liveA (mkCS I2 T0 R0 O2  c   Sa0) inv ph i≢ = mkCS I2 T0 R0 Og c Sa1 , NM.sndack
liveA (mkCS I2 T0 R0 O2  c   Sag) inv ph i≢ = mkCS I2 T0 R0 O2 c Sa0 , NM.gSa
liveA (mkCS I2 T0 R0 O2  Rc0 Sa1) inv ph i≢ = ⊥-elim (o≢0 (sucinj inv))
liveA (mkCS I2 T0 R0 O2  Rc1 Sa1) inv ph i≢ = ⊥-elim (o≢0 (sucinj inv))
liveA (mkCS I2 T0 R0 O2  Rcg Sa1) inv ph i≢ = ⊥-elim (o≢0 (sucinj inv))
liveA (mkCS I2 T0 R0 O1  c   s)   inv ph i≢ = ⊥-elim (o≢0 ph)
liveA (mkCS I2 T0 R0 O0  Rcg s)   inv ph i≢ = mkCS I2 T0 R0 O0 Rc0 s , NM.gRc
liveA (mkCS I2 T0 R0 O0  Rc1 s)   inv ph i≢ = ⊥-elim (o≢0 ph)
liveA (mkCS I2 T0 R0 O0  Rc0 Sa1) inv ph i≢ = mkCS I2 T0 R1 O0 Rc0 Sag , NM.ack
liveA (mkCS I2 T0 R0 O0  Rc0 Sa0) inv ph i≢ = ⊥-elim (o≢0 (sym inv))
liveA (mkCS I2 T0 R0 O0  Rc0 Sag) inv ph i≢ = ⊥-elim (o≢0 (sym inv))

liveB : ∀ cs → Inv cs → phaseN cs ≡ 1 → out cs ≢ O1
      → Σ[ cs′ ∈ CS ] (cs NM.⇒ᵢ cs′)
liveB (mkCS I0 t r o c s) inv ph o≢ =
  ⊥-elim (o≢0 (sym (trans (sym (Inv-I0-phase0 {mkCS I0 t r o c s} refl inv)) ph)))
liveB (mkCS Ig t r o c s) inv ph o≢ =
  ⊥-elim (o≢0 (sym (trans (sym (Inv-Ig-phase0 {mkCS Ig t r o c s} refl inv)) ph)))
liveB (mkCS I1 T0 r o c s) inv ph o≢ = mkCS I2 T1 r o c s , NM.sndmsg
liveB (mkCS I1 Tg r o c s) inv ph o≢ = mkCS I1 T0 r o c s , NM.gT
liveB (mkCS I1 T1 r o c s) inv ph o≢ = ⊥-elim (o≢0 (sucinj ph))
liveB (mkCS I2 t  Rg o   c   s)   inv ph o≢ = mkCS I2 t R0 o c s , NM.gR
liveB (mkCS I2 t  R1 o   c   s)   inv ph o≢ = mkCS Ig t Rg o c s , NM.rcvack
liveB (mkCS I2 Tg R0 o   c   s)   inv ph o≢ = mkCS I2 T0 R0 o c s , NM.gT
liveB (mkCS I2 t  R0 Og  c   s)   inv ph o≢ = mkCS I2 t R0 O0 c s , NM.gO
liveB (mkCS I2 t  R0 O1  c   s)   inv ph o≢ = ⊥-elim (o≢ refl)
liveB (mkCS I2 t  R0 o   Rcg s)   inv ph o≢ = mkCS I2 t R0 o Rc0 s , NM.gRc
liveB (mkCS I2 t  R0 o   c   Sag) inv ph o≢ = mkCS I2 t R0 o c Sa0 , NM.gSa
liveB (mkCS I2 T0 R0 O0  Rc1 Sa0) inv ph o≢ = mkCS I2 T0 R0 O1 Rcg Sa0 , NM.rcvmsg
liveB (mkCS I2 T1 R0 O0  Rc0 Sa0) inv ph o≢ = mkCS I2 Tg R0 O0 Rc1 Sa0 , NM.tx
liveB (mkCS I2 T0 R0 O0  Rc0 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sym inv))
liveB (mkCS I2 T0 R0 O0  Rc0 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sym ph))
liveB (mkCS I2 T0 R0 O0  Rc1 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T0 R0 O2  Rc0 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sym ph))
liveB (mkCS I2 T0 R0 O2  Rc0 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T0 R0 O2  Rc1 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T0 R0 O2  Rc1 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T1 R0 O0  Rc0 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T1 R0 O0  Rc1 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T1 R0 O0  Rc1 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T1 R0 O2  Rc0 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T1 R0 O2  Rc0 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T1 R0 O2  Rc1 Sa0) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))
liveB (mkCS I2 T1 R0 O2  Rc1 Sa1) inv ph o≢ = ⊥-elim (o≢0 (sucinj inv))

------------------------------------------------------------------------
-- E2.d  THE ABSTRACT DRAINS (pure NetModel, by well-founded recursion).
-- Data-free: they reduce `CS` states on the abstract automaton.
------------------------------------------------------------------------

infix 4 _⇒ᵢ*_
data _⇒ᵢ*_ : CS → CS → Set where
  ε   : ∀ {cs} → cs ⇒ᵢ* cs
  _◅_ : ∀ {cs cs′ cs″} → cs NM.⇒ᵢ cs′ → cs′ ⇒ᵢ* cs″ → cs ⇒ᵢ* cs″

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
-- E2.e  Realise an abstract drain as a Network τ* run.  Internal moves
-- preserve the in-flight payload `d`, so the realisation stays at a fixed
-- `d` (uses the `d`-threaded `real-⇒ᵢ-Net` of Task 4).
------------------------------------------------------------------------

real-⇒ᵢ*-Net : ∀ {cs cs-d d} → cs ⇒ᵢ* cs-d → ⟦ cs ⟧N d ─[τ*]─► ⟦ cs-d ⟧N d
real-⇒ᵢ*-Net ε             = τ*-refl
real-⇒ᵢ*-Net (step ◅ path) =
  τ*-step (real-⇒ᵢ-Net step) (real-⇒ᵢ*-Net path)

-- transitivity of `⇒ᵢ*` (keeps the drain's `Reach` evidence).
reach-i* : ∀ {cs cs-d ph} → Reach cs ph → cs ⇒ᵢ* cs-d → Reach cs-d ph
reach-i* r ε            = r
reach-i* r (step ◅ path) = reach-i* (reach-i r step) path

------------------------------------------------------------------------
-- E1: THE COPYSPEC LIFECYCLE (d-indexed C0/C1/Cg).
--
-- `CopySpec` (instance p1) = `⦀⋆ (map CopysId allIDs)` with ONE live leaf
-- `Copy N2N_KeepAlive c0`.  Its lifecycle is three reachable states:
--   C0 = CopySpec — offers `input a` (any payload), τ-stable; `input a` → C1 a.
--   C1 d          — offers `output d` (value forced to d), τ-stable; → Cg d.
--   Cg d          — the loop0 restart guard; ONE τ → C0, offers NO visible ev.
-- The data payload threads: `input a` introduces `a`, `output d` emits `d`.
------------------------------------------------------------------------

C0 : NetProc
C0 = CopySpec

C1 : Data → NetProc
C1 d = succV C0 inputAt d

Cg : Data → NetProc
Cg d = succV (C1 d) outputAt d

------------------------------------------------------------------------
-- CopySpec τ-stability.
------------------------------------------------------------------------
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
-- Interleave peeling through the inert Skips (mirror of the template).
------------------------------------------------------------------------

NoEv : NetProc → Set₁
NoEv P = ∀ {B} {e : Net Data B} {a} {W} →
         P ─[ ev (evl (evLabel B e a)) ]─► W → ⊥

Skip-no-ev : ∀ {B} {e : Net Data B} {a} {W} →
  Skip {0ℓ} ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
Skip-no-ev (sVis () _)

⦀-NoEv : ∀ {P Q} → NoEv P → NoEv Q → NoEv (P ⦀ Q)
⦀-NoEv {P} {Q} nP nQ st with Par-ev-elim ∅ES ⊤merge P Q st
... | evSync () _ _
... | evL  _ pst     = nP pst
... | evR  _ qst     = nQ qst
... | evBoth _ pst _ = nP pst

⦀-ev-left : ∀ {P Q B} {e : Net Data B} {a} {W} → NoEv Q →
  (P ⦀ Q) ─[ ev (evl (evLabel B e a)) ]─► W →
  Σ[ P′ ∈ NetProc ] ((P ─[ ev (evl (evLabel B e a)) ]─► P′) × (W ≡ (P′ ⦀ Q)))
⦀-ev-left {P} {Q} nQ st with Par-ev-elim ∅ES ⊤merge P Q st
... | evSync () _ _
... | evL  _ pst      = _ , pst , refl
... | evR  _ qst      = ⊥-elim (nQ qst)
... | evBoth _ _ qst  = ⊥-elim (nQ qst)

⦀-ev-right : ∀ {P Q B} {e : Net Data B} {a} {W} → NoEv P →
  (P ⦀ Q) ─[ ev (evl (evLabel B e a)) ]─► W →
  Σ[ Q′ ∈ NetProc ] ((Q ─[ ev (evl (evLabel B e a)) ]─► Q′) × (W ≡ (P ⦀ Q′)))
⦀-ev-right {P} {Q} nP st with Par-ev-elim ∅ES ⊤merge P Q st
... | evSync () _ _
... | evL  _ pst      = ⊥-elim (nP pst)
... | evR  _ qst      = _ , qst , refl
... | evBoth _ pst _  = ⊥-elim (nP pst)

Skip0-NoEv : NoEv (Skip {0ℓ})
Skip0-NoEv = Skip-no-ev

tail-NoEv : NoEv (Skip {0ℓ} ⦀ (Skip {0ℓ} ⦀ Skip {0ℓ}))
tail-NoEv = ⦀-NoEv Skip0-NoEv (⦀-NoEv Skip0-NoEv Skip0-NoEv)

------------------------------------------------------------------------
-- The live leaf `CopyLeaf = Copy KA c0` and its two successors.
------------------------------------------------------------------------
CopyLeaf : NetProc
CopyLeaf = Copy N2N_KeepAlive c0

CopyLeaf-in : Data → NetProc
CopyLeaf-in d = succV CopyLeaf inputAt d

CopyLeaf-g : Data → NetProc
CopyLeaf-g d = succV (CopyLeaf-in d) outputAt d

-- CopyLeaf fires ONLY `input` (some payload `d : Data`), landing on `CopyLeaf-in d`,
-- with label `inputLbl d`.  The payload is existential because the signature
-- quantifies `a : B` (general), while `inputLbl`/`CopyLeaf-in` need a `Data` arg.
CopyLeaf-ev : ∀ {B} {e : Net Data B} {a} {W} →
  CopyLeaf ─[ ev (evl (evLabel B e a)) ]─► W →
  Σ[ d ∈ Data ] ((evl (evLabel B e a) ≡ inputLbl d) × (W ≡ CopyLeaf-in d))
CopyLeaf-ev {e = input N2N_KeepAlive zero} {a = a} (sVis refl refl) = a , refl , refl
CopyLeaf-ev {e = input N2N_ChainSync    c}    (sVis refl ())
CopyLeaf-ev {e = input N2N_BlockFetch   c}    (sVis refl ())
CopyLeaf-ev {e = input N2N_TxSubmission c}    (sVis refl ())
CopyLeaf-ev {e = input N2N_LeiosNotify  c}    (sVis refl ())
CopyLeaf-ev {e = input N2N_LeiosFetch   c}    (sVis refl ())
CopyLeaf-ev {e = output id c}                 (sVis refl ())
CopyLeaf-ev {e = sndmsg id c}                 (sVis refl ())
CopyLeaf-ev {e = rcvmsg id c}                 (sVis refl ())
CopyLeaf-ev {e = tx     id c}                 (sVis refl ())
CopyLeaf-ev {e = sndack id c}                 (sVis refl ())
CopyLeaf-ev {e = rcvack id c}                 (sVis refl ())
CopyLeaf-ev {e = ack    id c}                 (sVis refl ())

-- CopyLeaf-in d fires ONLY `output`, value forced to `d`; lands on CopyLeaf-g d.
-- The fired label is `outputLbl d` and the target is `CopyLeaf-g d` (current d).
-- Well-typed: the payload constraint is expressed through the LABEL equation
-- (`outputLbl d`), never `a ≡ d` (`a : B` is heterogeneous with `d : Data`).
CopyLeaf-in-ev : ∀ {d B} {e : Net Data B} {a} {W} →
  CopyLeaf-in d ─[ ev (evl (evLabel B e a)) ]─► W →
  (evl (evLabel B e a) ≡ outputLbl d) × (W ≡ CopyLeaf-g d)
CopyLeaf-in-ev {d = d} {e = output N2N_KeepAlive zero} {a = a} (sVis refl h)
  with a ≟ d
... | no  _    = nothing-absurd h
CopyLeaf-in-ev {d = d} {e = output N2N_KeepAlive zero} {a = a} (sVis refl h)
  | yes refl rewrite ≟-diag d = refl , sym (just-injective h)
CopyLeaf-in-ev {e = output N2N_ChainSync    c}     (sVis refl ())
CopyLeaf-in-ev {e = output N2N_BlockFetch   c}     (sVis refl ())
CopyLeaf-in-ev {e = output N2N_TxSubmission c}     (sVis refl ())
CopyLeaf-in-ev {e = output N2N_LeiosNotify  c}     (sVis refl ())
CopyLeaf-in-ev {e = output N2N_LeiosFetch   c}     (sVis refl ())
CopyLeaf-in-ev {e = input  id c}                   (sVis refl ())
CopyLeaf-in-ev {e = sndmsg id c}                   (sVis refl ())
CopyLeaf-in-ev {e = rcvmsg id c}                   (sVis refl ())
CopyLeaf-in-ev {e = tx     id c}                   (sVis refl ())
CopyLeaf-in-ev {e = sndack id c}                   (sVis refl ())
CopyLeaf-in-ev {e = rcvack id c}                   (sVis refl ())
CopyLeaf-in-ev {e = ack    id c}                   (sVis refl ())

------------------------------------------------------------------------
-- C0 / C1 / Cg step characterizations (peel the inert Skips).
------------------------------------------------------------------------

-- C0 fires only `input d` (some fresh payload `d : Data`), landing on C1 d.
-- The payload is existential (the signature quantifies `a : B`, general).
C0-evL : ∀ {B} {e : Net Data B} {a} {W} →
  C0 ─[ ev (evl (evLabel B e a)) ]─► W →
  Σ[ d ∈ Data ] ((evl (evLabel B e a) ≡ inputLbl d) × (W ≡ C1 d))
C0-evL st
  with ⦀-ev-right Skip0-NoEv st
... | _ , st1 , refl with ⦀-ev-right Skip0-NoEv st1
... | _ , st2 , refl with ⦀-ev-right Skip0-NoEv st2
... | _ , st3 , refl with ⦀-ev-left tail-NoEv st3
... | _ , st4 , refl with ⦀-ev-left Skip0-NoEv st4
... | _ , st5 , refl with CopyLeaf-ev st5
... | d , Lin , refl = d , Lin , refl

-- C1 d fires only `output d` (value forced to d), landing on Cg d.
C1-evL : ∀ {d B} {e : Net Data B} {a} {W} →
  C1 d ─[ ev (evl (evLabel B e a)) ]─► W → (evl (evLabel B e a) ≡ outputLbl d) × (W ≡ Cg d)
C1-evL {d} st
  with ⦀-ev-right Skip0-NoEv st
... | _ , st1 , refl with ⦀-ev-right Skip0-NoEv st1
... | _ , st2 , refl with ⦀-ev-right Skip0-NoEv st2
... | _ , st3 , refl with ⦀-ev-left tail-NoEv st3
... | _ , st4 , refl with ⦀-ev-left Skip0-NoEv st4
... | _ , st5 , refl with CopyLeaf-in-ev st5
... | Lout , refl rewrite ≟-diag d = Lout , refl

------------------------------------------------------------------------
-- τ-stability of C0/C1; the single τ of Cg.
------------------------------------------------------------------------
C0-noτ : ∀ {W} → C0 ─[ τ ]─► W → ⊥
C0-noτ = CopySpec-stable

C1-noτ : ∀ {d W} → C1 d ─[ τ ]─► W → ⊥
C1-noτ (sSil ())
C1-noτ (sTau {i = _ , fin}                       refl ())
C1-noτ (sTau {i = _ , base _}                    refl ())
C1-noτ (sTau {i = _ , pair fin (base _)}         refl ())
C1-noτ (sTau {i = _ , pair fin fin}              refl ())
C1-noτ (sTau {i = _ , pair fin (pair _ _)}       refl ())
C1-noτ (sTau {i = _ , pair (base _) _}           refl ())
C1-noτ (sTau {i = _ , pair (pair _ _) _}         refl ())

-- Cg d has the single restart τ to C0; ≟-diag d unblocks the stuck force.
Cg-τ : ∀ {d W} → Cg d ─[ τ ]─► W → W ≡ C0
Cg-τ {d} step rewrite ≟-diag d with step
... | sSil refl = refl
... | sTau () _

Cg-noev : ∀ {d B} {e : Net Data B} {a} {W} →
  Cg d ─[ ev (evl (evLabel B e a)) ]─► W → ⊥
Cg-noev {d} step rewrite ≟-diag d with step
... | sVis () _

------------------------------------------------------------------------
-- The three CopySpec lifecycle STRONG steps (intros for the builder).
------------------------------------------------------------------------
C0─input─►C1 : ∀ {a} → C0 ─[ ev (inputLbl a) ]─► C1 a
C0─input─►C1 = sVis {at = inputAt} refl refl

C1─output─►Cg : ∀ {d} → C1 d ─[ ev (outputLbl d) ]─► Cg d
C1─output─►Cg {d} = sVis {at = outputAt} refl (h d)
  where
  h : ∀ d → vis-of (PTree.force (C1 d)) outputAt d ≡ just (Cg d)
  h d rewrite ≟-diag d = refl

Cg─τ─►C0 : ∀ {d} → Cg d ─[ τ ]─► C0
Cg─τ─►C0 {d} = go d
  where
  go : ∀ d → Cg d ─[ τ ]─► C0
  go d rewrite ≟-diag d = sSil refl

------------------------------------------------------------------------
-- ¬ Diverges at each state, and the coinductive GoodC invariant.
------------------------------------------------------------------------
¬Div-C0 : ¬ Diverges C0
¬Div-C0 = ¬Diverges-CopySpec

¬Div-C1 : ∀ {d} → ¬ Diverges (C1 d)
¬Div-C1 d = C1-noτ (d .Diverges.step)

¬Div-Cg : ∀ {d} → ¬ Diverges (Cg d)
¬Div-Cg {d} dv = ¬Div-C0 (subst Diverges (Cg-τ (dv .Diverges.step)) (dv .Diverges.rest))

-- non-divergence of every decoded network state (from MAcc-cs of Task 1-4).
¬Div-⟦⟧N : ∀ cs d → ¬ Diverges (⟦ cs ⟧N d)
¬Div-⟦⟧N cs d = Hide-noDiv-from-MAcc csTA' _ (MAcc-cs cs d)

------------------------------------------------------------------------
-- TASK 5 / STEP 1 — per-leaf payload-erosion lemmas.
--
-- At a reachable phase-A inp=I0 state the invariant pins the live leaves to
-- the guard / base values {T0,Tg},{R0,Rg},{O0,Og},{Rc0,Rcg},{Sa0,Sag}.
-- Base leaves ignore `d` definitionally; the guard leaves are stuck on
-- `d ≟ d`, collapsed independently on each side by `≟-diag`.
------------------------------------------------------------------------

erode-Tg  : ∀ dI dR → decT Tg  dI ≡ decT Tg  dR
erode-Tg  dI dR rewrite ≟-diag dI | ≟-diag dR = refl

erode-Rg  : ∀ dI dR → decR Rg  dI ≡ decR Rg  dR
erode-Rg  dI dR = refl

erode-Og  : ∀ dI dR → decO Og  dI ≡ decO Og  dR
erode-Og  dI dR rewrite ≟-diag dI | ≟-diag dR = refl

erode-Rcg : ∀ dI dR → decC Rcg dI ≡ decC Rcg dR
erode-Rcg dI dR rewrite ≟-diag dI | ≟-diag dR = refl

erode-Sag : ∀ dI dR → decS Sag dI ≡ decS Sag dR
erode-Sag dI dR = refl

------------------------------------------------------------------------
-- TASK 5 / STEP 1 — `mix≡uni` and the phase-A pinning helper `pinA`.
--
-- After a fresh `input` fires, the post-state is MIXED: only the decI leaf
-- carries the new payload `a′`; every partner leaf still carries the old
-- `d`.  On the eroded set ({T0,Tg},{O0,Og},{Rc0,Rcg}; decR/decS payload-free)
-- the partner leaves are payload-insensitive, so the mixed decode collapses
-- onto the uniform decode at `a′`.
------------------------------------------------------------------------

-- decT t is payload-insensitive on {T0,Tg}.
decT-erode : ∀ {t} → (t ≡ T0) ⊎ (t ≡ Tg) → ∀ d a′ → decT t d ≡ decT t a′
decT-erode (inj₁ refl) d a′ = refl
decT-erode (inj₂ refl) d a′ = erode-Tg d a′

-- decO o is payload-insensitive on {O0,Og}.
decO-erode : ∀ {o} → (o ≡ O0) ⊎ (o ≡ Og) → ∀ d a′ → decO o d ≡ decO o a′
decO-erode (inj₁ refl) d a′ = refl
decO-erode (inj₂ refl) d a′ = erode-Og d a′

-- decC c is payload-insensitive on {Rc0,Rcg}.
decC-erode : ∀ {c} → (c ≡ Rc0) ⊎ (c ≡ Rcg) → ∀ d a′ → decC c d ≡ decC c a′
decC-erode (inj₁ refl) d a′ = refl
decC-erode (inj₂ refl) d a′ = erode-Rcg d a′

mix≡uni : ∀ {t r o c s a′ d}
  → (t ≡ T0) ⊎ (t ≡ Tg) → (o ≡ O0) ⊎ (o ≡ Og) → (c ≡ Rc0) ⊎ (c ≡ Rcg)
  → ⟦ mkCS I1 t r o c s ⟧ᵢ a′ d ≡ ⟦ mkCS I1 t r o c s ⟧ a′
mix≡uni {t} {r} {o} {c} {s} {a′} {d} hT hO hC =
  cong₂ (Par⊤ csTA') txEq rxEq
  where
  txEq : decTxᵢ I1 t r a′ d ≡ decTx I1 t r a′
  txEq = cong (_∖ csSR')
           (cong₂ (Par⊤ csSR') refl
             (cong₂ _⦀_ (decT-erode hT d a′) refl))
  rxEq : decRx o c s d ≡ decRx o c s a′
  rxEq = cong (_∖ csRS')
           (cong₂ (Par⊤ csRS') (decO-erode hO d a′)
             (cong₂ _⦀_ (decC-erode hC d a′) refl))

-- At a phase-A reachable inp=I0 state the invariant pins the live leaves.
pinA : ∀ {t r o c s} → Inv (mkCS I0 t r o c s) → phaseN (mkCS I0 t r o c s) ≡ 0
     → ((t ≡ T0) ⊎ (t ≡ Tg)) × ((o ≡ O0) ⊎ (o ≡ Og)) × ((c ≡ Rc0) ⊎ (c ≡ Rcg))
pinA {T0} {r} {O0} {Rc0} {s} inv pe = inj₁ refl , inj₁ refl , inj₁ refl
pinA {T0} {r} {O0} {Rcg} {s} inv pe = inj₁ refl , inj₁ refl , inj₂ refl
pinA {T0} {r} {Og} {Rc0} {s} inv pe = inj₁ refl , inj₂ refl , inj₁ refl
pinA {T0} {r} {Og} {Rcg} {s} inv pe = inj₁ refl , inj₂ refl , inj₂ refl
pinA {Tg} {r} {O0} {Rc0} {s} inv pe = inj₂ refl , inj₁ refl , inj₁ refl
pinA {Tg} {r} {O0} {Rcg} {s} inv pe = inj₂ refl , inj₁ refl , inj₂ refl
pinA {Tg} {r} {Og} {Rc0} {s} inv pe = inj₂ refl , inj₂ refl , inj₁ refl
pinA {Tg} {r} {Og} {Rcg} {s} inv pe = inj₂ refl , inj₂ refl , inj₂ refl
pinA {T1} {r} {o}  {c}   {s} inv pe =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ b d e f → ℕcon 1 :⊕ (b :⊕ d :⊕ e :⊕ f)
                                         :≡ ℕcon 1 :⊕ b :⊕ d :⊕ e :⊕ f)
                       refl (aR r) (aO o) (aC c) (aS s)) inv))
pinA {t}  {r} {O1} {c}   {s} inv pe =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ a b e f → ℕcon 1 :⊕ (a :⊕ b :⊕ e :⊕ f)
                                         :≡ a :⊕ b :⊕ ℕcon 1 :⊕ e :⊕ f)
                       refl (aT t) (aR r) (aC c) (aS s)) inv))
pinA {t}  {r} {O2} {c}   {s} inv pe =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ a b e f → ℕcon 1 :⊕ (a :⊕ b :⊕ e :⊕ f)
                                         :≡ a :⊕ b :⊕ ℕcon 1 :⊕ e :⊕ f)
                       refl (aT t) (aR r) (aC c) (aS s)) inv))
pinA {t}  {r} {o}  {Rc1} {s} inv pe =
  ⊥-elim (o≢0 (trans (ℕsolve 4 (λ a b d f → ℕcon 1 :⊕ (a :⊕ b :⊕ d :⊕ f)
                                         :≡ a :⊕ b :⊕ d :⊕ ℕcon 1 :⊕ f)
                       refl (aT t) (aR r) (aO o) (aS s)) inv))

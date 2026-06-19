{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Feasibility probe: the `evBoth` (par-brBoth) ⊓-overlap NEVER fires in
-- the single-channel `Network` parallel compositions.
--
-- `par-brBoth` (CSP.Operators, the `par-pVis` case `no _ | just | just`)
-- is taken iff some event `at`/`a` is OUTSIDE the node's sync set AND BOTH
-- operands offer it.  Each refl below witnesses, per parallel node and per
-- candidate non-sync event, that AT MOST ONE operand offers it (the other
-- yields `nothing`) — i.e. the operands' non-sync offered-alphabets are
-- DISJOINT.  Hence `par-pVis` always lands on the single-sided branch
-- (`just (Par …)`), never on the inline `react ∅v (par-brBoth …)`.
--
-- Covered nodes (single-channel instance p1, KeepAlive c0, Data = ⊤):
--   * Transmitter ⦀ RcvAck     (⦀ = empty sync set ⇒ ALL events non-sync)
--   * Receiver ⦀ SndAck        (dual)
--   * Par⊤ csTA TxSide RxSide  (top node; csTA = {tx, ack})
--   * the ⦀ Skip cruft of `Inputs`
-- This validates the "disjoint-alphabet / no-evBoth restricted cong-Par⊤"
-- route, which avoids up-to-expansion entirely (see the spike report).
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Fin using (zero)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Bool using (true)
open import Data.Product using (_,_; proj₁)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (PTree; NodeKind; react; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (IDs; N2N_KeepAlive)

module CSP.Examples.Cardano_network.EvBothProbe where
open PTree

instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

p1 : Params
p1 = record
  { Cookie = ⊤ ; Block = ⊤ ; Txid = ⊤ ; LSlot = ⊤
  ; VoterId = ⊤ ; LFBitmap = ⊤ ; VoteBlob = ⊤
  ; numConns = λ where N2N_KeepAlive → 1 ; _ → 0
  ; decCookie  = decEq⊤ ; decBlock = decEq⊤ ; decTxid = decEq⊤
  ; decLSlot = decEq⊤ ; decVoterId = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤ }

open import CSP.Examples.Cardano_network.Net p1
  using (Net; Conn; Net-≟; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack)
open import CSP.Examples.Cardano_network.Network p1 ⊤
import CSP.Operators {E = Net ⊤} (Net-≟ {⊤}) as Op

NetR : Set
NetR = Poly.⊤ {0ℓ}
c0 : Conn N2N_KeepAlive
c0 = zero

visCont : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR
        → (at : AnyTypes (Net ⊤)) → proj₁ at → Maybe (PTree (Net ⊤) (ExtI (Net ⊤)) NetR)
visCont (react v _) = v
visCont _           = λ _ _ → nothing

offers : NetProc → (at : AnyTypes (Net ⊤)) → proj₁ at → Set
offers P at a = is-just (visCont (force P) at a) ≡ true
noff   : NetProc → (at : AnyTypes (Net ⊤)) → proj₁ at → Set₁
noff   P at a = visCont (force P) at a ≡ nothing

at-input at-output at-sndmsg at-rcvmsg at-tx at-sndack at-rcvack at-ack
  : AnyTypes (Net ⊤)
at-input  = (⊤ , input  N2N_KeepAlive c0)
at-output = (⊤ , output N2N_KeepAlive c0)
at-sndmsg = (⊤ , sndmsg N2N_KeepAlive c0)
at-rcvmsg = (⊤ , rcvmsg N2N_KeepAlive c0)
at-tx     = (⊤ , tx     N2N_KeepAlive c0)
at-sndack = (⊤ , sndack N2N_KeepAlive c0)
at-rcvack = (⊤ , rcvack N2N_KeepAlive c0)
at-ack    = (⊤ , ack    N2N_KeepAlive c0)

-- ===== Transmitter ⦀ RcvAck  (empty sync set: ALL events non-sync) =====
T-sndmsg : offers Transmitter at-sndmsg tt
T-sndmsg = refl
T-ack-no : noff Transmitter at-ack tt
T-ack-no = refl
R-ack    : offers RcvAck at-ack tt
R-ack    = refl
R-sndmsg-no : noff RcvAck at-sndmsg tt
R-sndmsg-no = refl
TR-sndmsg : offers (Transmitter Op.⦀ RcvAck) at-sndmsg tt
TR-sndmsg = refl
TR-ack    : offers (Transmitter Op.⦀ RcvAck) at-ack tt
TR-ack    = refl

-- ===== Receiver ⦀ SndAck =====
Rc-tx : offers Receiver at-tx tt
Rc-tx = refl
Rc-sndack-no : noff Receiver at-sndack tt
Rc-sndack-no = refl
SA-sndack : offers SndAck at-sndack tt
SA-sndack = refl
SA-tx-no : noff SndAck at-tx tt
SA-tx-no = refl

-- ===== TxSide / RxSide top-level disjoint on non-sync (csTA={tx,ack}) =====
TxSide-input : offers TxSide at-input tt
TxSide-input = refl
RxSide-input-no : noff RxSide at-input tt
RxSide-input-no = refl
-- initially RxSide also offers nothing at `output` (must await rcvmsg first);
-- TxSide offers nothing at `output` ⇒ no both-offer on any non-sync event.
RxSide-output-no : noff RxSide at-output tt
RxSide-output-no = refl
TxSide-output-no : noff TxSide at-output tt
TxSide-output-no = refl

-- ===== Skip-interleaving cruft is harmless: Skip offers nothing, so the
--        ⦀Fin/⦀⋆ folds (… ⦀ Skip ⦀ Skip …) never contribute a second offer. =====
Skip-input-no : noff (Op.Skip) at-input tt
Skip-input-no = refl
-- Inputs = Input KA c0 ⦀ Skip ⦀ … ⦀ Skip still offers input single-sidedly:
Inputs-input : offers Inputs at-input tt
Inputs-input = refl

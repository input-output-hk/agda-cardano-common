{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C — THE NON-VACUITY WITNESS (owner decision
-- D3-a): a trace of the REAL two-node system `rawSys2` in which node 0
-- forges a block and node 1 deposits it, the block having crossed the link
-- through ChainSync, BlockFetch and the medium.  Node 1 never forges on the
-- trace, so its deposit came across the link.
--
-- LEVEL: `rawSys2` itself — the unhidden composite `noLivelock2` is about —
-- not a node and not a sub-composite.
--
-- THE RUN (25 visible events, six medium messages, all on link 0's `hi`
-- cells, where node 1's clients and node 0's servers sit):
--   node 0 forges `nothing` (no EB; `forgeOK` holds and `rbCert nothing ≡
--   nothing`, so the store deposits it at the forge); node 1's client thread
--   asks for the next header; MsgCSRequestNext crosses; node 0's server
--   thread reads index 0 and answers AwaitReply then RollForward (both
--   cross); node 1 requests the block's range; MsgRequestRange crosses;
--   node 0 serves StartBatch and Block (both cross); node 1's client thread
--   receives the block and deposits it (`stPut` at node 1).
--
-- PROOF TECHNIQUE: no step of a composite is ever computed.  Each LEAF
-- component (a thread, a store, a peer at its own alphabet, a medium cell)
-- gets its own trace, by `refl` steps on a concrete state or, where a value
-- is a variable, by the generic `outS`/`preS`/`iterEv` steps; the leaves are
-- assembled with EXACT-endpoint versions of the trace-intro lemmas (`ParX`,
-- `HideX`, `renX`, built on `Par-sync`/`Par-soloL-reach`/`Par-soloR-reach`/
-- `Par-τ-*`, `Hide-*`, `ren-*-fwd`) and explicit interleaving witnesses.
-- The medium lemma is generic in the payload and the cell's protocol, so one
-- proof carries all six messages.
--
-- Import-by-nobody.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.NoLivelock.Live2 where

open import Level using (0ℓ)
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; ExtI; AnyTypes; react)
open import Cardano_network.Base
open import Cardano_network.Parametric.Leios.LeiosInstance2 using (p2; lp2; line2; rawSys2)
open import Cardano_network.Net p2
open import Cardano_network.Data p2
  using ( Payload; DecEq-Payload; header; tip; point; chainRange; chainSync; blockFetch
        ; MsgCSRequestNext; MsgCSAwaitReply; MsgCSRollForward
        ; MsgRequestRange; MsgStartBatch; MsgBlock )
open import Cardano_network.Params using (module Params)
open Params p2 using (time₀; length₀)
open import Cardano_network.ApiAlphabet p2 using (apiES)
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic p2 line2 apiES using (homeOf)

------------------------------------------------------------------------
-- Generic lifts with EXACT endpoints, over any alphabet (hoisted to
-- `CSP.Laws.Traces.TraceIntroExact` in Stage L, L7)
------------------------------------------------------------------------

open import CSP.Laws.Traces.TraceIntroExact using (module GX; module RX)

------------------------------------------------------------------------
-- The medium: one message on a `hi` cell of link 0, from its start back to its start
------------------------------------------------------------------------

open import Cardano_network.NetCommon p2 using (ιNet; ιNet⁻¹; ιNet-linv; ioES; NetworkLinkA)
open import Cardano_network.Network p2 Payload
  using (inputMenu; outputMenu; csSR; csSR-dec; csRS; csRS-dec; csTA; csTA-dec)
  renaming (Input to InCell; Output to OutCell)
open import Cardano_network.NetworkLink p2 Payload
  using ( NetworkLink; NetOneLink; TxSideₗ; RxSideₗ; Inputsₗ; Outputsₗ
        ; Transmitterₗ; RcvAckₗ; Receiverₗ; SndAckₗ )
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as NO
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN
import Semantics.Failures {E = Net Payload} {I = ExtI (Net Payload)} as FN
import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as FA
-- the generic lifts at the medium's own alphabet
module GN = GX (Net-≟ {Payload})
-- the medium's renaming into the composite's alphabet
module RN = RX {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv

-- a medium event
nv : ∀ {X} → Net Payload X → X → LN.Event√ (⊤ {0ℓ})
nv e a = LN.evl (LN.evLabel _ e a)

-- the `hi` input cell of protocol `id` on link 0 answers its own `input`, whatever the payload
inMenu : ∀ id x → inputMenu fzero hi id (_ , input fzero hi id) x
                ≡ just (NO.Output (sndmsg fzero hi id) x (NO.Prefix₀ (rcvack fzero hi id) NO.Skip))
inMenu id x with id ≟ id
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- the `hi` output cell of protocol `id` on link 0 answers its own `rcvmsg`, whatever the payload
outMenu : ∀ id x → outputMenu fzero hi id (_ , rcvmsg fzero hi id) x
                 ≡ just (NO.Output (output fzero hi id) x (NO.Prefix₀ (sndack fzero hi id) NO.Skip))
outMenu id x with id ≟ id
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- the input cell's part of one message
InTr : IDs → Payload → Set₁
InTr id m = Inputsₗ fzero FN.⟹⟨ nv (input fzero hi id) m ∷ nv (sndmsg fzero hi id) m ∷ nv (rcvack fzero hi id) U.tt ∷ [] ⟩ Inputsₗ fzero

-- the output cell's part of one message
OutTr : IDs → Payload → Set₁
OutTr id m = Outputsₗ fzero FN.⟹⟨ nv (rcvmsg fzero hi id) m ∷ nv (output fzero hi id) m ∷ nv (sndack fzero hi id) U.tt ∷ [] ⟩ Outputsₗ fzero

-- the medium's traces, with the medium-alphabet lifts opened
module Med where
  open GN

  -- the input cell takes `m` in, forwards it, takes the acknowledgement, and is back at its start
  inCellTr : ∀ id m → InCell fzero hi id FN.⟹⟨ nv (input fzero hi id) m ∷ nv (sndmsg fzero hi id) m ∷ nv (rcvack fzero hi id) U.tt ∷ [] ⟩ InCell fzero hi id
  inCellTr id m =
    FN.⟹-ev (rndEv (LN.sVis refl (inMenu id m)))
    (FN.⟹-ev (rndEv (outS (sndmsg fzero hi id) m _))
    (FN.⟹-ev (rndEv (preS (rcvack fzero hi id) _ U.tt))
    (FN.⟹-τ (LN.sSil refl) FN.⟹-refl)))

  -- the output cell takes `m` from the receiver, hands it out, acknowledges, and is back at its start
  outCellTr : ∀ id m → OutCell fzero hi id FN.⟹⟨ nv (rcvmsg fzero hi id) m ∷ nv (output fzero hi id) m ∷ nv (sndack fzero hi id) U.tt ∷ [] ⟩ OutCell fzero hi id
  outCellTr id m =
    FN.⟹-ev (rndEv (LN.sVis refl (outMenu id m)))
    (FN.⟹-ev (rndEv (outS (output fzero hi id) m _))
    (FN.⟹-ev (rndEv (preS (sndack fzero hi id) _ U.tt))
    (FN.⟹-τ (LN.sSil refl) FN.⟹-refl)))

  -- the transmitter passes `m` on as a `tx`
  trTr : ∀ id m → Transmitterₗ fzero FN.⟹⟨ nv (sndmsg fzero hi id) m ∷ nv (tx fzero hi id) m ∷ [] ⟩ Transmitterₗ fzero
  trTr id m =
    FN.⟹-ev (LN.sVis refl refl) (FN.⟹-ev (rndEv (outS (tx fzero hi id) m _)) (FN.⟹-τ (LN.sSil refl) FN.⟹-refl))

  -- the acknowledgement receiver passes the `ack` on as a `rcvack`
  raTr : ∀ id → RcvAckₗ fzero FN.⟹⟨ nv (ack fzero hi id) U.tt ∷ nv (rcvack fzero hi id) U.tt ∷ [] ⟩ RcvAckₗ fzero
  raTr id =
    FN.⟹-ev (LN.sVis refl refl) (FN.⟹-ev (rndEv (preS (rcvack fzero hi id) _ U.tt)) (FN.⟹-τ (LN.sSil refl) FN.⟹-refl))

  -- the receiver passes the `tx` on as a `rcvmsg`
  rcTr : ∀ id m → Receiverₗ fzero FN.⟹⟨ nv (tx fzero hi id) m ∷ nv (rcvmsg fzero hi id) m ∷ [] ⟩ Receiverₗ fzero
  rcTr id m =
    FN.⟹-ev (LN.sVis refl refl) (FN.⟹-ev (rndEv (outS (rcvmsg fzero hi id) m _)) (FN.⟹-τ (LN.sSil refl) FN.⟹-refl))

  -- the acknowledgement sender passes the `sndack` on as an `ack`
  saTr : ∀ id → SndAckₗ fzero FN.⟹⟨ nv (sndack fzero hi id) U.tt ∷ nv (ack fzero hi id) U.tt ∷ [] ⟩ SndAckₗ fzero
  saTr id =
    FN.⟹-ev (LN.sVis refl refl) (FN.⟹-ev (rndEv (preS (ack fzero hi id) _ U.tt)) (FN.⟹-τ (LN.sSil refl) FN.⟹-refl))

  -- ONE MESSAGE: `m` enters on the `hi` cell of protocol `id` and leaves on it; every
  -- internal hand-over (sndmsg/tx/rcvmsg, sndack/ack/rcvack) is hidden, and the medium is
  -- back at its start
  medMsg : ∀ id m → InTr id m → OutTr id m
         → NetworkLink FN.⟹⟨ nv (input fzero hi id) m ∷ nv (output fzero hi id) m ∷ [] ⟩ NetworkLink
  medMsg id m ins outs =
    ⦀L (HideX (NO.chanSet csTA csTA-dec)
          (ParX (NO.chanSet csTA csTA-dec) txS rxS (lf (λ ()) (sy _ (rt (λ ()) (sy _ pn)))))
          (kp (λ ()) (dp _ (kp (λ ()) (dp _ hn))))) _
    where
      -- the transmitting side: in, forwarded, acknowledged
      txS : TxSideₗ fzero FN.⟹⟨ nv (input fzero hi id) m ∷ nv (tx fzero hi id) m ∷ nv (ack fzero hi id) U.tt ∷ [] ⟩ TxSideₗ fzero
      txS = HideX (NO.chanSet csSR csSR-dec)
              (ParX (NO.chanSet csSR csSR-dec) ins
                 (ParX NO.∅ES (trTr id m) (raTr id) (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ()) pn)))))
                 (lf (λ ()) (sy _ (rt (λ ()) (rt (λ ()) (sy _ pn))))))
              (kp (λ ()) (dp _ (kp (λ ()) (kp (λ ()) (dp _ hn)))))
      -- the receiving side: received, out, acknowledged
      rxS : RxSideₗ fzero FN.⟹⟨ nv (tx fzero hi id) m ∷ nv (output fzero hi id) m ∷ nv (ack fzero hi id) U.tt ∷ [] ⟩ RxSideₗ fzero
      rxS = HideX (NO.chanSet csRS csRS-dec)
              (ParX (NO.chanSet csRS csRS-dec) outs
                 (ParX NO.∅ES (rcTr id m) (saTr id) (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ()) pn)))))
                 (rt (λ ()) (sy _ (lf (λ ()) (sy _ (rt (λ ()) pn))))))
              (kp (λ ()) (dp _ (kp (λ ()) (dp _ (kp (λ ()) hn)))))

  -- the ChainSync input cell is the fourth of link 0's twelve
  insCS : ∀ m → InTr N2N_ChainSync m
  insCS m = ⦀R (⦀R (⦀R (⦀L (inCellTr N2N_ChainSync m) _) _) _) _

  -- the ChainSync output cell likewise
  outsCS : ∀ m → OutTr N2N_ChainSync m
  outsCS m = ⦀R (⦀R (⦀R (⦀L (outCellTr N2N_ChainSync m) _) _) _) _

  -- the BlockFetch input cell is the sixth
  insBF : ∀ m → InTr N2N_BlockFetch m
  insBF m = ⦀R (⦀R (⦀R (⦀R (⦀R (⦀L (inCellTr N2N_BlockFetch m) _) _) _) _) _) _

  -- the BlockFetch output cell likewise
  outsBF : ∀ m → OutTr N2N_BlockFetch m
  outsBF m = ⦀R (⦀R (⦀R (⦀R (⦀R (⦀L (outCellTr N2N_BlockFetch m) _) _) _) _) _) _

  -- a ChainSync message across the renamed medium
  csMsg : ∀ m → NetworkLinkA FA.⟹⟨ RN.rmap (nv (input fzero hi N2N_ChainSync) m ∷ nv (output fzero hi N2N_ChainSync) m ∷ []) ⟩ NetworkLinkA
  csMsg m = RN.renX (medMsg N2N_ChainSync m (insCS m) (outsCS m)) _

  -- a BlockFetch message across the renamed medium
  bfMsg : ∀ m → NetworkLinkA FA.⟹⟨ RN.rmap (nv (input fzero hi N2N_BlockFetch) m ∷ nv (output fzero hi N2N_BlockFetch) m ∷ []) ⟩ NetworkLinkA
  bfMsg m = RN.renX (medMsg N2N_BlockFetch m (insBF m) (outsBF m)) _

------------------------------------------------------------------------
-- The composite's alphabet
------------------------------------------------------------------------

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (labels; Σc)

------------------------------------------------------------------------
-- The counts the statement names
------------------------------------------------------------------------

-- whether two directions agree
sameDir : Dir → Dir → Bool
sameDir lo lo = true
sameDir hi hi = true
sameDir _  _  = false

-- node `n`'s home direction (on the line, a node is identified by it)
homeDir : Fin 2 → Dir
homeDir n = proj₂ (homeOf n)

-- forges at node `n`
cForgeAt : Fin 2 → Event → ℕ
cForgeAt n (evLabel _ (env _ d envForge) _) = if sameDir d (homeDir n) then 1 else 0
cForgeAt n _                                = 0

-- deposits into node `n`'s RB store
cPutAt : Fin 2 → Event → ℕ
cPutAt n (evLabel _ (store _ d stPut) _) = if sameDir d (homeDir n) then 1 else 0
cPutAt n _                               = 0

------------------------------------------------------------------------
-- The run's payloads and events
------------------------------------------------------------------------

open import Cardano_network.Data p2 using (Header; Tip; ChainRange)

-- the forged block's header and tip
hd : Header × Tip
hd = header nothing , tip nothing

-- the forged block's one-point range
rng : ChainRange
rng = chainRange (point nothing) (point nothing)

-- the six wire messages
mReqNext mAwait mRollF mReqRange mStart mBlock : Payload
mReqNext  = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext
mAwait    = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply
mRollF    = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header nothing) (tip nothing))
mReqRange = time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange rng)
mStart    = time₀ , FromResponder , length₀ , blockFetch MsgStartBatch
mBlock    = time₀ , FromResponder , length₀ , blockFetch (MsgBlock nothing)

-- an event of the composite
aev : ∀ {X} → Net_Api Payload X → X → Event√ (⊤ {0ℓ})
aev e a = evl (evLabel _ e a)

-- THE 25 EVENTS, in run order (node 0's home is `(0 , lo)`, node 1's `(0 , hi)`; every
-- api and wire event is at direction `hi`)
fg c1 i1 o1 s1 g0 s2 i2 o2 s3 i3 o3 c2 c3 i4 o4 s4 s5 i5 o5 s6 i6 o6 c4 pt : Event√ (⊤ {0ℓ})
fg = aev (env fzero lo envForge) (nothing , nothing)              -- node 0 forges `nothing`
c1 = aev (apiCS fzero hi sendCSRequestNext) U.tt                  -- node 1 asks for the next header
i1 = aev (input fzero hi N2N_ChainSync) mReqNext                 -- … onto the wire
o1 = aev (output fzero hi N2N_ChainSync) mReqNext                -- … off the wire at node 0
s1 = aev (apiCS fzero hi reqCSRequestNext) U.tt                   -- node 0's server thread takes it
g0 = aev (store fzero lo (stGetAt 0)) nothing                     -- … reads index 0 of its store
s2 = aev (apiCS fzero hi sendCSAwaitReply) U.tt                   -- … answers AwaitReply
i2 = aev (input fzero hi N2N_ChainSync) mAwait
o2 = aev (output fzero hi N2N_ChainSync) mAwait
s3 = aev (apiCS fzero hi sendCSRollForward) hd                    -- … then RollForward
i3 = aev (input fzero hi N2N_ChainSync) mRollF
o3 = aev (output fzero hi N2N_ChainSync) mRollF
c2 = aev (apiCS fzero hi recvCSRollforward) hd                    -- node 1 receives the header
c3 = aev (apiBF fzero hi sendBFRequestRange) rng                  -- … requests the block
i4 = aev (input fzero hi N2N_BlockFetch) mReqRange
o4 = aev (output fzero hi N2N_BlockFetch) mReqRange
s4 = aev (apiBF fzero hi reqBFRange) rng                          -- node 0 takes the request
s5 = aev (apiBF fzero hi sendBFStartBatch) U.tt                   -- … starts the batch
i5 = aev (input fzero hi N2N_BlockFetch) mStart
o5 = aev (output fzero hi N2N_BlockFetch) mStart
s6 = aev (apiBF fzero hi sendBFBlock) nothing                     -- … sends the block
i6 = aev (input fzero hi N2N_BlockFetch) mBlock
o6 = aev (output fzero hi N2N_BlockFetch) mBlock
c4 = aev (apiBF fzero hi recvBFBlock) nothing                     -- node 1 receives the block
pt = aev (store fzero hi stPut) nothing                           -- … and DEPOSITS it

-- the run
sAll : List (Event√ (⊤ {0ℓ}))
sAll = fg ∷ c1 ∷ i1 ∷ o1 ∷ s1 ∷ g0 ∷ s2 ∷ i2 ∷ o2 ∷ s3 ∷ i3 ∷ o3 ∷ c2 ∷ c3 ∷ i4 ∷ o4 ∷ s4 ∷ s5
     ∷ i5 ∷ o5 ∷ s6 ∷ i6 ∷ o6 ∷ c4 ∷ pt ∷ []

------------------------------------------------------------------------
-- The peers, each at its own alphabet
------------------------------------------------------------------------

open import Cardano_network.ChainSync p2
  using (CSEv; sendCS; receiveCS; apiCSev; CSclientStClient; CSserverStClient)
open import Cardano_network.BlockFetch p2
  using (BFEv; sendBF; receiveBF; apiBFev; BFclientStClient; BFserverStClient)
open import Cardano_network.NetworkPar p2 using (ιCS; ιCS⁻¹; ιCS-linv; ιBF; ιBF⁻¹; ιBF-linv)
import Semantics.LTS {E = CSEv} {I = ExtI CSEv} as LC
import Semantics.Failures {E = CSEv} {I = ExtI CSEv} as FC
import Semantics.LTS {E = BFEv} {I = ExtI BFEv} as LB
import Semantics.Failures {E = BFEv} {I = ExtI BFEv} as FB
-- the ChainSync peers' renaming
module RC = RX {E₁ = CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv
-- the BlockFetch peers' renaming
module RB = RX {E₁ = BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv

-- a ChainSync peer event
cv : ∀ {X} → CSEv X → X → LC.Event√ (⊤ {0ℓ})
cv e a = LC.evl (LC.evLabel _ e a)

-- a BlockFetch peer event
bv : ∀ {X} → BFEv X → X → LB.Event√ (⊤ {0ℓ})
bv e a = LB.evl (LB.evLabel _ e a)

-- node 1's ChainSync client: RequestNext out, AwaitReply in, RollForward in and reported
csCli : FC.traces (CSclientStClient fzero hi)
          ( cv (apiCSev fzero hi sendCSRequestNext) U.tt ∷ cv (sendCS fzero hi) mReqNext
          ∷ cv (receiveCS fzero hi) mAwait ∷ cv (receiveCS fzero hi) mRollF
          ∷ cv (apiCSev fzero hi recvCSRollforward) hd ∷ [])
csCli = _ ,
  FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) FC.⟹-refl))))))

-- node 0's ChainSync server: RequestNext in and reported, AwaitReply and RollForward out
csSrv : FC.traces (CSserverStClient fzero hi)
          ( cv (receiveCS fzero hi) mReqNext ∷ cv (apiCSev fzero hi reqCSRequestNext) U.tt
          ∷ cv (apiCSev fzero hi sendCSAwaitReply) U.tt ∷ cv (sendCS fzero hi) mAwait
          ∷ cv (apiCSev fzero hi sendCSRollForward) hd ∷ cv (sendCS fzero hi) mRollF ∷ [])
csSrv = _ ,
  FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) FC.⟹-refl)))))))

-- node 1's BlockFetch client: RequestRange out, StartBatch and Block in, Block reported
bfCli : FB.traces (BFclientStClient fzero hi)
          ( bv (apiBFev fzero hi sendBFRequestRange) rng ∷ bv (sendBF fzero hi) mReqRange
          ∷ bv (receiveBF fzero hi) mStart ∷ bv (receiveBF fzero hi) mBlock
          ∷ bv (apiBFev fzero hi recvBFBlock) nothing ∷ [])
bfCli = _ ,
  FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) FB.⟹-refl))))))

-- node 0's BlockFetch server: RequestRange in and reported, StartBatch and Block out
bfSrv : FB.traces (BFserverStClient fzero hi)
          ( bv (receiveBF fzero hi) mReqRange ∷ bv (apiBFev fzero hi reqBFRange) rng
          ∷ bv (apiBFev fzero hi sendBFStartBatch) U.tt ∷ bv (sendBF fzero hi) mStart
          ∷ bv (apiBFev fzero hi sendBFBlock) nothing ∷ bv (sendBF fzero hi) mBlock ∷ [])
bfSrv = _ ,
  FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) FB.⟹-refl)))))))

------------------------------------------------------------------------
-- The threads and the RB stores
------------------------------------------------------------------------

import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic p2 lp2 line2 apiES (λ n → n) using (forgeL; serverLoopL; blockStoreL; nodeLogicL; st₀)
open NL.Generic p2 line2 apiES using (clientLoop; storeES)
open import Cardano_network.Parametric.Leios.PeersP p2 using (nodeBundleP)
open import Cardano_network.Parametric.Leios.LeiosInstance2 using (node2)

-- node 0's forge thread forges `nothing` (no EB)
fgTr : traces (forgeL fzero) (fg ∷ [])
fgTr = _ , ⟹-ev (sVis refl refl) ⟹-refl

-- node 0's ChainSync/BlockFetch server thread, pointer 0: one round up to the block
srvTr : traces (serverLoopL fzero (fzero , lo)) (s1 ∷ g0 ∷ s2 ∷ s3 ∷ s4 ∷ s5 ∷ s6 ∷ [])
srvTr = _ ,
  ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
  (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) ⟹-refl))))))

-- node 0's RB store: the forge deposits `nothing`, then index 0 hands it out
st0Tr : traces (blockStoreL fzero []) (fg ∷ g0 ∷ [])
st0Tr = _ , ⟹-ev (sVis refl refl) (⟹-τ (sSil refl) (⟹-ev (sVis refl refl) ⟹-refl))

-- node 1's client thread: one round, up to the deposit
cliTr : traces (clientLoop (fsuc fzero) (fzero , hi)) (c1 ∷ c2 ∷ c3 ∷ c4 ∷ pt ∷ [])
cliTr = _ ,
  ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
  (⟹-ev (sVis refl refl) ⟹-refl))))

-- node 1's RB store takes the deposit
st1Tr : traces (blockStoreL (fsuc fzero) []) (pt ∷ [])
st1Tr = _ , ⟹-ev (sVis refl refl) ⟹-refl

------------------------------------------------------------------------
-- The assembly (no composite step is ever computed)
------------------------------------------------------------------------

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as NO′
open NO′ using (_⦀_)
-- the generic lifts at the composite's alphabet
module GA = GX (Net_Api-≟ {Payload})
open GA using (PI; pn; sy; lf; rt; ParX; ⦀L; ⦀R; ⦀LR)
open import CSP.Laws.FD.BindFD (Net_Api-≟ {Payload}) using (⟹-trans)

-- the medium carries the six messages
medTr : NetworkLinkA ⟹⟨ i1 ∷ o1 ∷ i2 ∷ o2 ∷ i3 ∷ o3 ∷ i4 ∷ o4 ∷ i5 ∷ o5 ∷ i6 ∷ o6 ∷ [] ⟩ NetworkLinkA
medTr = ⟹-trans (Med.csMsg mReqNext) (⟹-trans (Med.csMsg mAwait) (⟹-trans (Med.csMsg mRollF)
          (⟹-trans (Med.bfMsg mReqRange) (⟹-trans (Med.bfMsg mStart) (Med.bfMsg mBlock)))))

-- node 0's peer bundle: its ChainSync server (fourth), then its BlockFetch server (sixth)
b0Tr : traces (nodeBundleP fzero lo hi) (o1 ∷ s1 ∷ s2 ∷ i2 ∷ s3 ∷ i3 ∷ o4 ∷ s4 ∷ s5 ∷ i5 ∷ s6 ∷ i6 ∷ [])
b0Tr = _ , ⦀R (⦀R (⦀R (⦀LR (RC.renX (proj₂ csSrv) _) (⦀R (⦀L (RB.renX (proj₂ bfSrv) _) _) _) _ _) _) _) _

-- node 1's peer bundle: its ChainSync client (fourth), then its BlockFetch client (sixth)
b1Tr : traces (nodeBundleP fzero hi lo) (c1 ∷ i1 ∷ o2 ∷ o3 ∷ c2 ∷ c3 ∷ i4 ∷ o5 ∷ o6 ∷ c4 ∷ [])
b1Tr = _ , ⦀R (⦀R (⦀R (⦀LR (RC.renX (proj₂ csCli) _) (⦀R (⦀L (RB.renX (proj₂ bfCli) _) _) _) _ _) _) _) _

-- node 0's logic: the forge and the server thread against the RB store
l0Tr : traces (nodeLogicL fzero st₀) (fg ∷ s1 ∷ g0 ∷ s2 ∷ s3 ∷ s4 ∷ s5 ∷ s6 ∷ [])
l0Tr = _ , ParX storeES
  (⦀LR (proj₂ fgTr) (⦀R (⦀R (⦀R (⦀R (⦀R (⦀L (proj₂ srvTr) _) _) _) _) _) _) _ _)
  (⦀L (proj₂ st0Tr) _)
  (sy _ (lf (λ ()) (sy _ (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) pn))))))))

-- node 1's logic: the client thread against the RB store
l1Tr : traces (nodeLogicL (fsuc fzero) st₀) (c1 ∷ c2 ∷ c3 ∷ c4 ∷ pt ∷ [])
l1Tr = _ , ParX storeES
  (⦀R (⦀R (⦀R (⦀R (⦀R (⦀L (proj₂ cliTr) _) _) _) _) _) _)
  (⦀L (proj₂ st1Tr) _)
  (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (sy _ pn)))))

-- node 0: bundle against logic on the api alphabet
n0Tr : traces (node2 fzero) (fg ∷ o1 ∷ s1 ∷ g0 ∷ s2 ∷ i2 ∷ s3 ∷ i3 ∷ o4 ∷ s4 ∷ s5 ∷ i5 ∷ s6 ∷ i6 ∷ [])
n0Tr = _ , ParX apiES (proj₂ b0Tr) (proj₂ l0Tr)
  (rt (λ ()) (lf (λ ()) (sy _ (rt (λ ()) (sy _ (lf (λ ()) (sy _ (lf (λ ()) (lf (λ ())
  (sy _ (sy _ (lf (λ ()) (sy _ (lf (λ ()) pn))))))))))))))

-- node 1: bundle against logic on the api alphabet
n1Tr : traces (node2 (fsuc fzero)) (c1 ∷ i1 ∷ o2 ∷ o3 ∷ c2 ∷ c3 ∷ i4 ∷ o5 ∷ o6 ∷ c4 ∷ pt ∷ [])
n1Tr = _ , ParX apiES (proj₂ b1Tr) (proj₂ l1Tr)
  (sy _ (lf (λ ()) (lf (λ ()) (lf (λ ()) (sy _ (sy _ (lf (λ ()) (lf (λ ()) (lf (λ ()) (sy _ (rt (λ ()) pn)))))))))))

-- the two nodes, interleaved
nsTr : traces (node2 fzero ⦀ node2 (fsuc fzero)) sAll
nsTr = _ , ParX NO′.∅ES (proj₂ n0Tr) (proj₂ n1Tr)
  (lf (λ ()) (rt (λ ()) (rt (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (rt (λ ())
  (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ())
  (lf (λ ()) (rt (λ ()) (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) pn)))))))))))))))))))))))))

------------------------------------------------------------------------
-- THE WITNESS
------------------------------------------------------------------------

-- NON-VACUITY (spec §7, owner decision D3-a): `rawSys2` has a trace with a forge at node 0,
-- NO forge at node 1, and a deposit into node 1's RB store — the block crossed the link
live2 : Σ[ s ∈ List (Event√ (⊤ {0ℓ})) ] traces rawSys2 s
          × (1 ≤ Σc (cForgeAt fzero) (labels s)) × (Σc (cForgeAt (fsuc fzero)) (labels s) ≡ 0)
          × (1 ≤ Σc (cPutAt (fsuc fzero)) (labels s))
live2 = sAll , (_ , ParX ioES medTr (proj₂ nsTr) top) , s≤s z≤n , refl , s≤s z≤n
  where
    -- the medium synchronises on every wire event; the nodes take the rest alone
    top : PI ioES (i1 ∷ o1 ∷ i2 ∷ o2 ∷ i3 ∷ o3 ∷ i4 ∷ o4 ∷ i5 ∷ o5 ∷ i6 ∷ o6 ∷ []) sAll sAll
    top = rt (λ ()) (rt (λ ()) (sy _ (sy _ (rt (λ ()) (rt (λ ()) (rt (λ ()) (sy _ (sy _ (rt (λ ())
          (sy _ (sy _ (rt (λ ()) (rt (λ ()) (sy _ (sy _ (rt (λ ()) (rt (λ ()) (sy _ (sy _ (rt (λ ())
          (sy _ (sy _ (rt (λ ()) (rt (λ ()) pn))))))))))))))))))))))))

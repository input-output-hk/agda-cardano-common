{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage L — THE NON-VACUITY WITNESS ACROSS BOTH LINKS
-- (owner decision, L2 check-in): a trace of the SHIPPED three-node line in
-- which node A (node 0) forges a block, node B (node 1) receives it over
-- link 0 and deposits it, and node C (node 2) receives it from B over
-- link 1 and deposits it.  Neither B nor C forges, and no `break` fires.
--
-- LEVEL: the unhidden composite `rawL` (`liveL`) AND the shipped system
-- `leiosSystemL = rawL ∖ ioES` itself (`liveL∖`, through `HideX`).
--
-- THE RUN (49 visible events; 24 wire events, twelve medium messages, all
-- on the `hi` cells of their link, where the clients and the servers of the
-- link's two ends sit): A forges `nothing`; then Stage C's `Live2` run on
-- link 0 with A serving B (ChainSync RequestNext / AwaitReply / RollForward,
-- BlockFetch RequestRange / StartBatch / Block), ending in B's `stPut`; then
-- the same run on link 1 with B serving C — B's endpoint-(1 , lo) server
-- thread reads index 0 of B's RB store, i.e. the block B has just deposited.
--
-- PROOF TECHNIQUE (Stage C's): no step of a composite is ever computed.  Each
-- LEAF component (a thread, a store, a peer at its own alphabet, a medium
-- cell) gets its own trace, by `refl` steps on a concrete state or by the
-- generic `outS`/`preS`/`rndEv` steps; leaves are assembled with the exact-
-- endpoint lifts of `CSP.Laws.Traces.TraceIntroExact` (`ParX`, `HideX`,
-- `renX`, and `△X` through each link's `break` interrupt) and explicit
-- interleaving witnesses.
--
-- Import-by-nobody.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.NoLivelock.LiveL where

open import Level using (0ℓ)
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Properties as FinP
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; s≤s; z≤n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF)
open import Cardano_network.Parametric.Leios.LeiosInstance3 using (rawL)
import Cardano_network.Parametric.Leios.LeiosInstanceL as LIL
open LIL using (leiosLLine)
open import Cardano_network.Net (pL 2 3)
open import Cardano_network.Data (pL 2 3)
  using ( Payload; DecEq-Payload; header; tip; point; chainRange; chainSync; blockFetch
        ; MsgCSRequestNext; MsgCSAwaitReply; MsgCSRollForward
        ; MsgRequestRange; MsgStartBatch; MsgBlock; Header; Tip; ChainRange )
open import Cardano_network.Params using (module Params)
open Params (pL 2 3) using (time₀; length₀)
open import Cardano_network.ApiAlphabet (pL 2 3) using (apiES)
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic (pL 2 3) leiosLLine apiES using (homeOf; clientLoop; storeES)
open import CSP.Laws.Traces.TraceIntroExact using (module GX; module RX)

-- the line's two links
l0 l1 : Link
l0 = fzero
l1 = fsuc fzero

-- the line's three nodes (A—B over link 0, B—C over link 1)
nA nB nC : Fin 3
nA = fzero
nB = fsuc fzero
nC = fsuc (fsuc fzero)

------------------------------------------------------------------------
-- The medium: one message on a `hi` cell of link `l`, from its start back to its start
------------------------------------------------------------------------

open import Cardano_network.NetCommon (pL 2 3)
  using (ιNet; ιNet⁻¹; ιNet-linv; ioES; NetworkLinkBreakableA; breakableNetLinkA)
open import Cardano_network.Network (pL 2 3) Payload
  using (inputMenu; outputMenu; csSR; csSR-dec; csRS; csRS-dec; csTA; csTA-dec)
  renaming (Input to InCell; Output to OutCell)
open import Cardano_network.NetworkLink (pL 2 3) Payload
  using ( NetOneLink; TxSideₗ; RxSideₗ; Inputsₗ; Outputsₗ
        ; Transmitterₗ; RcvAckₗ; Receiverₗ; SndAckₗ
        ; transmitterMenuₗ; rcvackMenuₗ; receiverMenuₗ; sndackMenuₗ )
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as NO
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN
import Semantics.Failures {E = Net Payload} {I = ExtI (Net Payload)} as FN
-- the generic lifts at the medium's own alphabet
module GN = GX (Net-≟ {Payload})
-- the medium's renaming into the composite's alphabet
module RN = RX {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv
-- the generic lifts at the composite's alphabet
module GA = GX (Net_Api-≟ {Payload})

-- a medium event
nv : ∀ {X} → Net Payload X → X → LN.Event√ (⊤ {0ℓ})
nv e a = LN.evl (LN.evLabel _ e a)

-- link `l`'s `hi` input cell of protocol `id` answers its own `input`, whatever the payload
inMenu : ∀ l id x → inputMenu l hi id (_ , input l hi id) x
                  ≡ just (NO.Output (sndmsg l hi id) x (NO.Prefix₀ (rcvack l hi id) NO.Skip))
inMenu l id x with l ≟ l
... | no ¬p    = ⊥-elim (¬p refl)
... | yes refl with id ≟ id
...   | yes refl = refl
...   | no ¬p    = ⊥-elim (¬p refl)

-- link `l`'s `hi` output cell of protocol `id` answers its own `rcvmsg`, whatever the payload
outMenu : ∀ l id x → outputMenu l hi id (_ , rcvmsg l hi id) x
                   ≡ just (NO.Output (output l hi id) x (NO.Prefix₀ (sndack l hi id) NO.Skip))
outMenu l id x with l ≟ l
... | no ¬p    = ⊥-elim (¬p refl)
... | yes refl with id ≟ id
...   | yes refl = refl
...   | no ¬p    = ⊥-elim (¬p refl)

-- link `l`'s transmitter takes its own `sndmsg`
trMenu : ∀ l id x → transmitterMenuₗ l (_ , sndmsg l hi id) x ≡ just (NO.Output (tx l hi id) x NO.Skip)
trMenu l id x with l ≟ l
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- link `l`'s acknowledgement receiver takes its own `ack`
raMenu : ∀ l id → rcvackMenuₗ l (_ , ack l hi id) U.tt ≡ just (NO.Prefix₀ (rcvack l hi id) NO.Skip)
raMenu l id with l ≟ l
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- link `l`'s receiver takes its own `tx`
rcMenu : ∀ l id x → receiverMenuₗ l (_ , tx l hi id) x ≡ just (NO.Output (rcvmsg l hi id) x NO.Skip)
rcMenu l id x with l ≟ l
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- link `l`'s acknowledgement sender takes its own `sndack`
saMenu : ∀ l id → sndackMenuₗ l (_ , sndack l hi id) U.tt ≡ just (NO.Prefix₀ (ack l hi id) NO.Skip)
saMenu l id with l ≟ l
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- the input cell's part of one message
InTr : Link → IDs → Payload → Set₁
InTr l id m = Inputsₗ l FN.⟹⟨ nv (input l hi id) m ∷ nv (sndmsg l hi id) m ∷ nv (rcvack l hi id) U.tt ∷ [] ⟩ Inputsₗ l

-- the output cell's part of one message
OutTr : Link → IDs → Payload → Set₁
OutTr l id m = Outputsₗ l FN.⟹⟨ nv (rcvmsg l hi id) m ∷ nv (output l hi id) m ∷ nv (sndack l hi id) U.tt ∷ [] ⟩ Outputsₗ l

-- the medium's traces, with the medium-alphabet lifts opened
module Med where
  open GN

  -- the input cell takes `m` in, forwards it, takes the acknowledgement, and is back at its start
  inCellTr : ∀ l id m → InCell l hi id FN.⟹⟨ nv (input l hi id) m ∷ nv (sndmsg l hi id) m ∷ nv (rcvack l hi id) U.tt ∷ [] ⟩ InCell l hi id
  inCellTr l id m =
    FN.⟹-ev (rndEv (LN.sVis refl (inMenu l id m)))
    (FN.⟹-ev (rndEv (outS (sndmsg l hi id) m _))
    (FN.⟹-ev (rndEv (preS (rcvack l hi id) _ U.tt))
    (FN.⟹-τ (LN.sSil refl) FN.⟹-refl)))

  -- the output cell takes `m` from the receiver, hands it out, acknowledges, and is back at its start
  outCellTr : ∀ l id m → OutCell l hi id FN.⟹⟨ nv (rcvmsg l hi id) m ∷ nv (output l hi id) m ∷ nv (sndack l hi id) U.tt ∷ [] ⟩ OutCell l hi id
  outCellTr l id m =
    FN.⟹-ev (rndEv (LN.sVis refl (outMenu l id m)))
    (FN.⟹-ev (rndEv (outS (output l hi id) m _))
    (FN.⟹-ev (rndEv (preS (sndack l hi id) _ U.tt))
    (FN.⟹-τ (LN.sSil refl) FN.⟹-refl)))

  -- the transmitter passes `m` on as a `tx`
  trTr : ∀ l id m → Transmitterₗ l FN.⟹⟨ nv (sndmsg l hi id) m ∷ nv (tx l hi id) m ∷ [] ⟩ Transmitterₗ l
  trTr l id m =
    FN.⟹-ev (rndEv (LN.sVis refl (trMenu l id m))) (FN.⟹-ev (rndEv (outS (tx l hi id) m _)) (FN.⟹-τ (LN.sSil refl) FN.⟹-refl))

  -- the acknowledgement receiver passes the `ack` on as a `rcvack`
  raTr : ∀ l id → RcvAckₗ l FN.⟹⟨ nv (ack l hi id) U.tt ∷ nv (rcvack l hi id) U.tt ∷ [] ⟩ RcvAckₗ l
  raTr l id =
    FN.⟹-ev (rndEv (LN.sVis refl (raMenu l id))) (FN.⟹-ev (rndEv (preS (rcvack l hi id) _ U.tt)) (FN.⟹-τ (LN.sSil refl) FN.⟹-refl))

  -- the receiver passes the `tx` on as a `rcvmsg`
  rcTr : ∀ l id m → Receiverₗ l FN.⟹⟨ nv (tx l hi id) m ∷ nv (rcvmsg l hi id) m ∷ [] ⟩ Receiverₗ l
  rcTr l id m =
    FN.⟹-ev (rndEv (LN.sVis refl (rcMenu l id m))) (FN.⟹-ev (rndEv (outS (rcvmsg l hi id) m _)) (FN.⟹-τ (LN.sSil refl) FN.⟹-refl))

  -- the acknowledgement sender passes the `sndack` on as an `ack`
  saTr : ∀ l id → SndAckₗ l FN.⟹⟨ nv (sndack l hi id) U.tt ∷ nv (ack l hi id) U.tt ∷ [] ⟩ SndAckₗ l
  saTr l id =
    FN.⟹-ev (rndEv (LN.sVis refl (saMenu l id))) (FN.⟹-ev (rndEv (preS (ack l hi id) _ U.tt)) (FN.⟹-τ (LN.sSil refl) FN.⟹-refl))

  -- ONE MESSAGE on link `l`: `m` enters on the `hi` cell of protocol `id` and leaves on it;
  -- every internal hand-over is hidden, and the link is back at its start
  medMsg : ∀ l id m → InTr l id m → OutTr l id m
         → NetOneLink l FN.⟹⟨ nv (input l hi id) m ∷ nv (output l hi id) m ∷ [] ⟩ NetOneLink l
  medMsg l id m ins outs =
    HideX (NO.chanSet csTA csTA-dec)
      (ParX (NO.chanSet csTA csTA-dec) txS rxS (lf (λ ()) (sy _ (rt (λ ()) (sy _ pn)))))
      (kp (λ ()) (dp _ (kp (λ ()) (dp _ hn))))
    where
      -- the transmitting side: in, forwarded, acknowledged
      txS : TxSideₗ l FN.⟹⟨ nv (input l hi id) m ∷ nv (tx l hi id) m ∷ nv (ack l hi id) U.tt ∷ [] ⟩ TxSideₗ l
      txS = HideX (NO.chanSet csSR csSR-dec)
              (ParX (NO.chanSet csSR csSR-dec) ins
                 (ParX NO.∅ES (trTr l id m) (raTr l id) (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ()) pn)))))
                 (lf (λ ()) (sy _ (rt (λ ()) (rt (λ ()) (sy _ pn))))))
              (kp (λ ()) (dp _ (kp (λ ()) (kp (λ ()) (dp _ hn)))))
      -- the receiving side: received, out, acknowledged
      rxS : RxSideₗ l FN.⟹⟨ nv (tx l hi id) m ∷ nv (output l hi id) m ∷ nv (ack l hi id) U.tt ∷ [] ⟩ RxSideₗ l
      rxS = HideX (NO.chanSet csRS csRS-dec)
              (ParX (NO.chanSet csRS csRS-dec) outs
                 (ParX NO.∅ES (rcTr l id m) (saTr l id) (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ()) pn)))))
                 (rt (λ ()) (sy _ (lf (λ ()) (sy _ (rt (λ ()) pn))))))
              (kp (λ ()) (dp _ (kp (λ ()) (dp _ (kp (λ ()) hn)))))

  -- the ChainSync input cell is the fourth of the link's twelve
  insCS : ∀ l m → InTr l N2N_ChainSync m
  insCS l m = ⦀R (⦀R (⦀R (⦀L (inCellTr l N2N_ChainSync m) _) _) _) _

  -- the ChainSync output cell likewise
  outsCS : ∀ l m → OutTr l N2N_ChainSync m
  outsCS l m = ⦀R (⦀R (⦀R (⦀L (outCellTr l N2N_ChainSync m) _) _) _) _

  -- the BlockFetch input cell is the sixth
  insBF : ∀ l m → InTr l N2N_BlockFetch m
  insBF l m = ⦀R (⦀R (⦀R (⦀R (⦀R (⦀L (inCellTr l N2N_BlockFetch m) _) _) _) _) _) _

  -- the BlockFetch output cell likewise
  outsBF : ∀ l m → OutTr l N2N_BlockFetch m
  outsBF l m = ⦀R (⦀R (⦀R (⦀R (⦀R (⦀L (outCellTr l N2N_BlockFetch m) _) _) _) _) _) _

------------------------------------------------------------------------
-- The composite's alphabet
------------------------------------------------------------------------

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (labels; Σc)
open import CSP.Laws.FD.BindFD (Net_Api-≟ {Payload}) using (⟹-trans)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as NO′
open NO′ using (_⦀_)
open GA using (PI; pn; sy; lf; rt; ParX; HideX; HT; hn; kp; dp; ⦀L; ⦀R; ⦀LR; △X; nq[]; nq∷)

-- ONE MESSAGE across link `l`'s breakable cell: the renamed link under its armed `break`
-- interrupt (the handler offers only `break l`, so it refuses both wire events)
msgB : ∀ l id m → InTr l id m → OutTr l id m
     → breakableNetLinkA l ⟹⟨ RN.rmap (nv (input l hi id) m ∷ nv (output l hi id) m ∷ []) ⟩ breakableNetLinkA l
msgB l id m ins outs = △X U.tt (RN.renX (Med.medMsg l id m ins outs) _) (nq∷ refl (nq∷ refl nq[]))

------------------------------------------------------------------------
-- The counts the statement names
------------------------------------------------------------------------

-- whether two directions agree
sameDir : Dir → Dir → Bool
sameDir lo lo = true
sameDir hi hi = true
sameDir _  _  = false

-- whether `(l , d)` is node `n`'s home endpoint (on the line, a node is identified by it)
atHome : Fin 3 → Link → Dir → Bool
atHome n l d = ⌊ FinP._≟_ l (proj₁ (homeOf n)) ⌋ ∧ sameDir d (proj₂ (homeOf n))

-- forges at node `n`
cForgeAt : Fin 3 → Event → ℕ
cForgeAt n (evLabel _ (env l d envForge) _) = if atHome n l d then 1 else 0
cForgeAt n _                                = 0

-- deposits into node `n`'s RB store
cPutAt : Fin 3 → Event → ℕ
cPutAt n (evLabel _ (store l d stPut) _) = if atHome n l d then 1 else 0
cPutAt n _                               = 0

-- link breaks
cBrk : Event → ℕ
cBrk (evLabel _ (break _) _) = 1
cBrk _                       = 0

------------------------------------------------------------------------
-- The run's payloads and events
------------------------------------------------------------------------

-- the forged block's header and tip
hd : Header × Tip
hd = header nothing , tip nothing

-- the forged block's one-point range
rng : ChainRange
rng = chainRange (point nothing) (point nothing)

-- the six wire messages of one link's run
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

-- THE 22 API AND WIRE EVENTS OF ONE LINK'S RUN (Live2's, at link `l`; every one at direction
-- `hi`): the client asks, the server reads (a store event, below), answers twice, serves the
-- block, the client receives it
c1 i1 o1 s1 s2 i2 o2 s3 i3 o3 c2 c3 i4 o4 s4 s5 i5 o5 s6 i6 o6 c4 : Link → Event√ (⊤ {0ℓ})
c1 l = aev (apiCS l hi sendCSRequestNext) U.tt                  -- the client asks for the next header
i1 l = aev (input l hi N2N_ChainSync) mReqNext                 -- … onto the wire
o1 l = aev (output l hi N2N_ChainSync) mReqNext                -- … off the wire at the server
s1 l = aev (apiCS l hi reqCSRequestNext) U.tt                   -- the server thread takes it
s2 l = aev (apiCS l hi sendCSAwaitReply) U.tt                   -- … answers AwaitReply
i2 l = aev (input l hi N2N_ChainSync) mAwait
o2 l = aev (output l hi N2N_ChainSync) mAwait
s3 l = aev (apiCS l hi sendCSRollForward) hd                    -- … then RollForward
i3 l = aev (input l hi N2N_ChainSync) mRollF
o3 l = aev (output l hi N2N_ChainSync) mRollF
c2 l = aev (apiCS l hi recvCSRollforward) hd                    -- the client receives the header
c3 l = aev (apiBF l hi sendBFRequestRange) rng                  -- … requests the block
i4 l = aev (input l hi N2N_BlockFetch) mReqRange
o4 l = aev (output l hi N2N_BlockFetch) mReqRange
s4 l = aev (apiBF l hi reqBFRange) rng                          -- the server takes the request
s5 l = aev (apiBF l hi sendBFStartBatch) U.tt                   -- … starts the batch
i5 l = aev (input l hi N2N_BlockFetch) mStart
o5 l = aev (output l hi N2N_BlockFetch) mStart
s6 l = aev (apiBF l hi sendBFBlock) nothing                     -- … sends the block
i6 l = aev (input l hi N2N_BlockFetch) mBlock
o6 l = aev (output l hi N2N_BlockFetch) mBlock
c4 l = aev (apiBF l hi recvBFBlock) nothing                     -- the client receives the block

-- THE STORE EVENTS (each at its node's home: A `(0 , lo)`, B `(0 , hi)`, C `(1 , hi)`)
fg gA ptB gB ptC : Event√ (⊤ {0ℓ})
fg  = aev (env l0 lo envForge) (nothing , nothing)              -- A forges `nothing` (no EB)
gA  = aev (store l0 lo (stGetAt 0)) nothing                     -- A's server reads index 0
ptB = aev (store l0 hi stPut) nothing                           -- B DEPOSITS the block
gB  = aev (store l0 hi (stGetAt 0)) nothing                     -- B's link-1 server reads index 0
ptC = aev (store l1 hi stPut) nothing                           -- C DEPOSITS the block

-- the run
sAll : List (Event√ (⊤ {0ℓ}))
sAll = fg ∷ c1 l0 ∷ i1 l0 ∷ o1 l0 ∷ s1 l0 ∷ gA ∷ s2 l0 ∷ i2 l0 ∷ o2 l0 ∷ s3 l0 ∷ i3 l0 ∷ o3 l0 ∷ c2 l0 ∷ c3 l0 ∷ i4 l0 ∷ o4 l0 ∷ s4 l0 ∷ s5 l0 ∷ i5 l0 ∷ o5 l0 ∷ s6 l0 ∷ i6 l0 ∷ o6 l0 ∷ c4 l0 ∷ ptB ∷ c1 l1 ∷ i1 l1 ∷ o1 l1 ∷ s1 l1 ∷ gB ∷ s2 l1 ∷ i2 l1 ∷ o2 l1 ∷ s3 l1 ∷ i3 l1 ∷ o3 l1 ∷ c2 l1 ∷ c3 l1 ∷ i4 l1 ∷ o4 l1 ∷ s4 l1 ∷ s5 l1 ∷ i5 l1 ∷ o5 l1 ∷ s6 l1 ∷ i6 l1 ∷ o6 l1 ∷ c4 l1 ∷ ptC ∷ []

-- the medium's part of it
sMed : List (Event√ (⊤ {0ℓ}))
sMed = i1 l0 ∷ o1 l0 ∷ i2 l0 ∷ o2 l0 ∷ i3 l0 ∷ o3 l0 ∷ i4 l0 ∷ o4 l0 ∷ i5 l0 ∷ o5 l0 ∷ i6 l0 ∷ o6 l0 ∷ i1 l1 ∷ o1 l1 ∷ i2 l1 ∷ o2 l1 ∷ i3 l1 ∷ o3 l1 ∷ i4 l1 ∷ o4 l1 ∷ i5 l1 ∷ o5 l1 ∷ i6 l1 ∷ o6 l1 ∷ []

-- one link's wire events
ioL : Link → List (Event√ (⊤ {0ℓ}))
ioL l = i1 l ∷ o1 l ∷ i2 l ∷ o2 l ∷ i3 l ∷ o3 l ∷ i4 l ∷ o4 l ∷ i5 l ∷ o5 l ∷ i6 l ∷ o6 l ∷ []

------------------------------------------------------------------------
-- The medium carries the twelve messages
------------------------------------------------------------------------

-- a ChainSync message across link `l`
csMsg : ∀ l m → breakableNetLinkA l ⟹⟨ RN.rmap (nv (input l hi N2N_ChainSync) m ∷ nv (output l hi N2N_ChainSync) m ∷ []) ⟩ breakableNetLinkA l
csMsg l m = msgB l N2N_ChainSync m (Med.insCS l m) (Med.outsCS l m)

-- a BlockFetch message across link `l`
bfMsg : ∀ l m → breakableNetLinkA l ⟹⟨ RN.rmap (nv (input l hi N2N_BlockFetch) m ∷ nv (output l hi N2N_BlockFetch) m ∷ []) ⟩ breakableNetLinkA l
bfMsg l m = msgB l N2N_BlockFetch m (Med.insBF l m) (Med.outsBF l m)

-- link `l` carries one run's six messages, and is back at its start, still unbroken
medL : ∀ l → breakableNetLinkA l ⟹⟨ ioL l ⟩ breakableNetLinkA l
medL l = ⟹-trans (csMsg l mReqNext) (⟹-trans (csMsg l mAwait) (⟹-trans (csMsg l mRollF)
           (⟹-trans (bfMsg l mReqRange) (⟹-trans (bfMsg l mStart) (bfMsg l mBlock)))))

-- the breakable medium: link 0's run, then link 1's
medTr : NetworkLinkBreakableA ⟹⟨ sMed ⟩ NetworkLinkBreakableA
medTr = ⦀LR (medL l0) (⦀L (medL l1) _) _ _

------------------------------------------------------------------------
-- The peers, each at its own alphabet
------------------------------------------------------------------------

open import Cardano_network.ChainSync (pL 2 3)
  using (CSEv; sendCS; receiveCS; apiCSev; CSclientStClient; CSserverStClient)
open import Cardano_network.BlockFetch (pL 2 3)
  using (BFEv; sendBF; receiveBF; apiBFev; BFclientStClient; BFserverStClient)
open import Cardano_network.NetworkPar (pL 2 3) using (ιCS; ιCS⁻¹; ιCS-linv; ιBF; ιBF⁻¹; ιBF-linv)
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

-- the client end's ChainSync client on link `l`: RequestNext out, AwaitReply in, RollForward in
-- and reported (one clause per link: the peer's menus decide the link)
csCli : ∀ l → FC.traces (CSclientStClient l hi)
          ( cv (apiCSev l hi sendCSRequestNext) U.tt ∷ cv (sendCS l hi) mReqNext
          ∷ cv (receiveCS l hi) mAwait ∷ cv (receiveCS l hi) mRollF
          ∷ cv (apiCSev l hi recvCSRollforward) hd ∷ [])
csCli fzero = _ ,
  FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) FC.⟹-refl))))))
csCli (fsuc fzero) = _ ,
  FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) FC.⟹-refl))))))

-- the server end's ChainSync server on link `l`: RequestNext in and reported, AwaitReply and
-- RollForward out
csSrv : ∀ l → FC.traces (CSserverStClient l hi)
          ( cv (receiveCS l hi) mReqNext ∷ cv (apiCSev l hi reqCSRequestNext) U.tt
          ∷ cv (apiCSev l hi sendCSAwaitReply) U.tt ∷ cv (sendCS l hi) mAwait
          ∷ cv (apiCSev l hi sendCSRollForward) hd ∷ cv (sendCS l hi) mRollF ∷ [])
csSrv fzero = _ ,
  FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) FC.⟹-refl)))))))
csSrv (fsuc fzero) = _ ,
  FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-τ (LC.sSil refl)
  (FC.⟹-ev (LC.sVis refl refl) (FC.⟹-ev (LC.sVis refl refl) FC.⟹-refl)))))))

-- the client end's BlockFetch client on link `l`: RequestRange out, StartBatch and Block in,
-- Block reported
bfCli : ∀ l → FB.traces (BFclientStClient l hi)
          ( bv (apiBFev l hi sendBFRequestRange) rng ∷ bv (sendBF l hi) mReqRange
          ∷ bv (receiveBF l hi) mStart ∷ bv (receiveBF l hi) mBlock
          ∷ bv (apiBFev l hi recvBFBlock) nothing ∷ [])
bfCli fzero = _ ,
  FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) FB.⟹-refl))))))
bfCli (fsuc fzero) = _ ,
  FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) FB.⟹-refl))))))

-- the server end's BlockFetch server on link `l`: RequestRange in and reported, StartBatch and
-- Block out
bfSrv : ∀ l → FB.traces (BFserverStClient l hi)
          ( bv (receiveBF l hi) mReqRange ∷ bv (apiBFev l hi reqBFRange) rng
          ∷ bv (apiBFev l hi sendBFStartBatch) U.tt ∷ bv (sendBF l hi) mStart
          ∷ bv (apiBFev l hi sendBFBlock) nothing ∷ bv (sendBF l hi) mBlock ∷ [])
bfSrv fzero = _ ,
  FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) FB.⟹-refl)))))))
bfSrv (fsuc fzero) = _ ,
  FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-τ (LB.sSil refl)
  (FB.⟹-ev (LB.sVis refl refl) (FB.⟹-ev (LB.sVis refl refl) FB.⟹-refl)))))))

------------------------------------------------------------------------
-- The threads and the RB stores
------------------------------------------------------------------------

import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic (pL 2 3) (lpF 2 3) leiosLLine apiES (λ n → n) using (forgeL; serverLoopL; blockStoreL; nodeLogicL; st₀)
open import Cardano_network.Parametric.Leios.PeersP (pL 2 3) using (nodeBundleP)
open import Cardano_network.Parametric.Node (pL 2 3) leiosLLine apiES using (nodeWith; Proc)

-- A's forge thread forges `nothing` (no EB)
fgTr : traces (forgeL nA) (fg ∷ [])
fgTr = _ , ⟹-ev (sVis refl refl) ⟹-refl

-- A's link-0 server thread, pointer 0: one round up to the block
srvA : traces (serverLoopL nA (l0 , lo)) (s1 l0 ∷ gA ∷ s2 l0 ∷ s3 l0 ∷ s4 l0 ∷ s5 l0 ∷ s6 l0 ∷ [])
srvA = _ ,
  ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
  (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) ⟹-refl))))))

-- B's link-1 server thread (its endpoint `(1 , lo)`), pointer 0: one round up to the block
srvB : traces (serverLoopL nB (l1 , lo)) (s1 l1 ∷ gB ∷ s2 l1 ∷ s3 l1 ∷ s4 l1 ∷ s5 l1 ∷ s6 l1 ∷ [])
srvB = _ ,
  ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
  (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) ⟹-refl))))))

-- B's link-0 client thread (its endpoint `(0 , hi)`): one round, up to the deposit
cliB : traces (clientLoop nB (l0 , hi)) (c1 l0 ∷ c2 l0 ∷ c3 l0 ∷ c4 l0 ∷ ptB ∷ [])
cliB = _ ,
  ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
  (⟹-ev (sVis refl refl) ⟹-refl))))

-- C's link-1 client thread: one round, up to the deposit
cliC : traces (clientLoop nC (l1 , hi)) (c1 l1 ∷ c2 l1 ∷ c3 l1 ∷ c4 l1 ∷ ptC ∷ [])
cliC = _ ,
  ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
  (⟹-ev (sVis refl refl) ⟹-refl))))

-- A's RB store: the forge deposits `nothing`, then index 0 hands it out
stA : traces (blockStoreL nA []) (fg ∷ gA ∷ [])
stA = _ , ⟹-ev (sVis refl refl) (⟹-τ (sSil refl) (⟹-ev (sVis refl refl) ⟹-refl))

-- B's RB store: B's client deposits `nothing`, then index 0 hands it to B's link-1 server
stB : traces (blockStoreL nB []) (ptB ∷ gB ∷ [])
stB = _ , ⟹-ev (sVis refl refl) (⟹-τ (sSil refl) (⟹-ev (sVis refl refl) ⟹-refl))

-- C's RB store takes the deposit
stC : traces (blockStoreL nC []) (ptC ∷ [])
stC = _ , ⟹-ev (sVis refl refl) ⟹-refl

------------------------------------------------------------------------
-- The assembly (no composite step is ever computed)
------------------------------------------------------------------------

-- the server end's peer bundle on link `l`: its ChainSync server (fourth), then its
-- BlockFetch server (sixth)
bSrv : ∀ l → traces (nodeBundleP l lo hi)
         (o1 l ∷ s1 l ∷ s2 l ∷ i2 l ∷ s3 l ∷ i3 l ∷ o4 l ∷ s4 l ∷ s5 l ∷ i5 l ∷ s6 l ∷ i6 l ∷ [])
bSrv l = _ , ⦀R (⦀R (⦀R (⦀LR (RC.renX (proj₂ (csSrv l)) _) (⦀R (⦀L (RB.renX (proj₂ (bfSrv l)) _) _) _) _ _) _) _) _

-- the client end's peer bundle on link `l`: its ChainSync client (fourth), then its
-- BlockFetch client (sixth)
bCli : ∀ l → traces (nodeBundleP l hi lo)
         (c1 l ∷ i1 l ∷ o2 l ∷ o3 l ∷ c2 l ∷ c3 l ∷ i4 l ∷ o5 l ∷ o6 l ∷ c4 l ∷ [])
bCli l = _ , ⦀R (⦀R (⦀R (⦀LR (RC.renX (proj₂ (csCli l)) _) (⦀R (⦀L (RB.renX (proj₂ (bfCli l)) _) _) _) _ _) _) _) _

-- A's logic: the forge and the link-0 server thread against the RB store
lgA : traces (nodeLogicL nA st₀) (fg ∷ s1 l0 ∷ gA ∷ s2 l0 ∷ s3 l0 ∷ s4 l0 ∷ s5 l0 ∷ s6 l0 ∷ [])
lgA = _ , ParX storeES
  (⦀LR (proj₂ fgTr) (⦀R (⦀R (⦀R (⦀R (⦀R (⦀L (proj₂ srvA) _) _) _) _) _) _) _ _)
  (⦀L (proj₂ stA) _)
  (sy _ (lf (λ ()) (sy _ (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) pn))))))))

-- B's logic: its endpoint-(0 , hi) client thread, then its endpoint-(1 , lo) server thread,
-- against the RB store
lgB : traces (nodeLogicL nB st₀) (c1 l0 ∷ c2 l0 ∷ c3 l0 ∷ c4 l0 ∷ ptB ∷ s1 l1 ∷ gB ∷ s2 l1 ∷ s3 l1 ∷ s4 l1 ∷ s5 l1 ∷ s6 l1 ∷ [])
lgB = _ , ParX storeES
  (⦀R (⦀R (⦀R (⦀R (⦀R (⦀LR (⦀L (proj₂ cliB) _) (⦀R (⦀L (proj₂ srvB) _) _) _ _) _) _) _) _) _)
  (⦀L (proj₂ stB) _)
  (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (sy _ (lf (λ ()) (sy _ (lf (λ ())
    (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) pn))))))))))))

-- C's logic: the client thread against the RB store
lgC : traces (nodeLogicL nC st₀) (c1 l1 ∷ c2 l1 ∷ c3 l1 ∷ c4 l1 ∷ ptC ∷ [])
lgC = _ , ParX storeES
  (⦀R (⦀R (⦀R (⦀R (⦀R (⦀L (proj₂ cliC) _) _) _) _) _) _)
  (⦀L (proj₂ stC) _)
  (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (sy _ pn)))))

-- a node of the shipped line: its link bundles against its logic on the api alphabet
nodeL : Fin 3 → Proc
nodeL n = nodeWith nodeBundleP n (nodeLogicL n st₀)

-- node A: its one bundle against its logic
trA : traces (nodeL nA) (fg ∷ o1 l0 ∷ s1 l0 ∷ gA ∷ s2 l0 ∷ i2 l0 ∷ s3 l0 ∷ i3 l0 ∷ o4 l0 ∷ s4 l0 ∷ s5 l0 ∷ i5 l0 ∷ s6 l0 ∷ i6 l0 ∷ [])
trA = _ , ParX apiES (proj₂ (bSrv l0)) (proj₂ lgA)
  (rt (λ ()) (lf (λ ()) (sy _ (rt (λ ()) (sy _ (lf (λ ()) (sy _ (lf (λ ())
    (lf (λ ()) (sy _ (sy _ (lf (λ ()) (sy _ (lf (λ ()) pn))))))))))))))

-- node B: its client-end bundle on link 0 and its server-end bundle on link 1, against its logic
trB : traces (nodeL nB) (c1 l0 ∷ i1 l0 ∷ o2 l0 ∷ o3 l0 ∷ c2 l0 ∷ c3 l0 ∷ i4 l0 ∷ o5 l0 ∷ o6 l0 ∷ c4 l0 ∷ ptB ∷ o1 l1 ∷ s1 l1 ∷ gB ∷ s2 l1 ∷ i2 l1 ∷ s3 l1 ∷ i3 l1 ∷ o4 l1 ∷ s4 l1 ∷ s5 l1 ∷ i5 l1 ∷ s6 l1 ∷ i6 l1 ∷ [])
trB = _ , ParX apiES (⦀LR (proj₂ (bCli l0)) (proj₂ (bSrv l1)) _ _) (proj₂ lgB)
  (sy _ (lf (λ ()) (lf (λ ()) (lf (λ ()) (sy _ (sy _ (lf (λ ()) (lf (λ ())
    (lf (λ ()) (sy _ (rt (λ ()) (lf (λ ()) (sy _ (rt (λ ()) (sy _ (lf (λ ())
    (sy _ (lf (λ ()) (lf (λ ()) (sy _ (sy _ (lf (λ ()) (sy _ (lf (λ ()) pn))))))))))))))))))))))))

-- node C: its one bundle against its logic
trC : traces (nodeL nC) (c1 l1 ∷ i1 l1 ∷ o2 l1 ∷ o3 l1 ∷ c2 l1 ∷ c3 l1 ∷ i4 l1 ∷ o5 l1 ∷ o6 l1 ∷ c4 l1 ∷ ptC ∷ [])
trC = _ , ParX apiES (proj₂ (bCli l1)) (proj₂ lgC)
  (sy _ (lf (λ ()) (lf (λ ()) (lf (λ ()) (sy _ (sy _ (lf (λ ()) (lf (λ ())
    (lf (λ ()) (sy _ (rt (λ ()) pn)))))))))))

-- nodes B and C, interleaved
trBC : traces (nodeL nB ⦀ nodeL nC) (c1 l0 ∷ i1 l0 ∷ o2 l0 ∷ o3 l0 ∷ c2 l0 ∷ c3 l0 ∷ i4 l0 ∷ o5 l0 ∷ o6 l0 ∷ c4 l0 ∷ ptB ∷ c1 l1 ∷ i1 l1 ∷ o1 l1 ∷ s1 l1 ∷ gB ∷ s2 l1 ∷ i2 l1 ∷ o2 l1 ∷ s3 l1 ∷ i3 l1 ∷ o3 l1 ∷ c2 l1 ∷ c3 l1 ∷ i4 l1 ∷ o4 l1 ∷ s4 l1 ∷ s5 l1 ∷ i5 l1 ∷ o5 l1 ∷ s6 l1 ∷ i6 l1 ∷ o6 l1 ∷ c4 l1 ∷ ptC ∷ [])
trBC = _ , ParX NO′.∅ES (proj₂ trB) (proj₂ trC)
  (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ())
    (lf (λ ()) (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ())
    (lf (λ ()) (lf (λ ()) (rt (λ ()) (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ())
    (rt (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (rt (λ ()) (lf (λ ()) (lf (λ ())
    (rt (λ ()) (rt (λ ()) (rt (λ ()) pn)))))))))))))))))))))))))))))))))))

-- the run of the unhidden composite
rawTr : traces rawL sAll
rawTr = _ , ParX ioES medTr (ParX NO′.∅ES (proj₂ trA) (proj₂ trBC)
  ((lf (λ ()) (rt (λ ()) (rt (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ()) (lf (λ ())
    (rt (λ ()) (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (lf (λ ())
    (lf (λ ()) (lf (λ ()) (lf (λ ()) (rt (λ ()) (lf (λ ()) (lf (λ ()) (rt (λ ()) (rt (λ ())
    (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ())
    (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ())
    (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ()) (rt (λ ())
    (rt (λ ()) pn)))))))))))))))))))))))))))))))))))))))))))))))))))
  (rt (λ ()) (rt (λ ()) (sy _ (sy _ (rt (λ ()) (rt (λ ()) (rt (λ ()) (sy _
    (sy _ (rt (λ ()) (sy _ (sy _ (rt (λ ()) (rt (λ ()) (sy _ (sy _
    (rt (λ ()) (rt (λ ()) (sy _ (sy _ (rt (λ ()) (sy _ (sy _ (rt (λ ())
    (rt (λ ()) (rt (λ ()) (sy _ (sy _ (rt (λ ()) (rt (λ ()) (rt (λ ()) (sy _
    (sy _ (rt (λ ()) (sy _ (sy _ (rt (λ ()) (rt (λ ()) (sy _ (sy _
    (rt (λ ()) (rt (λ ()) (sy _ (sy _ (rt (λ ()) (sy _ (sy _ (rt (λ ())
    (rt (λ ()) pn)))))))))))))))))))))))))))))))))))))))))))))))))

------------------------------------------------------------------------
-- THE WITNESSES
------------------------------------------------------------------------

-- the pins: a forge at A and at neither B nor C, a deposit at B and at C, no link break
Pins : List (Event√ (⊤ {0ℓ})) → Set
Pins s = (1 ≤ Σc (cForgeAt nA) (labels s)) × (Σc (cForgeAt nB) (labels s) ≡ 0) × (Σc (cForgeAt nC) (labels s) ≡ 0)
       × (1 ≤ Σc (cPutAt nB) (labels s)) × (1 ≤ Σc (cPutAt nC) (labels s)) × (Σc cBrk (labels s) ≡ 0)

-- NON-VACUITY ACROSS BOTH LINKS, at the unhidden composite: `rawL` has a trace in which A
-- forges, neither B nor C forges, B and then C deposit, and no link breaks — the block crossed
-- link 0 and then link 1 through B's RB store
liveL : Σ[ s ∈ List (Event√ (⊤ {0ℓ})) ] traces rawL s × Pins s
liveL = sAll , rawTr , s≤s z≤n , refl , refl , s≤s z≤n , s≤s z≤n , refl

-- the run with its wire events hidden
sHid : List (Event√ (⊤ {0ℓ}))
sHid = fg ∷ c1 l0 ∷ s1 l0 ∷ gA ∷ s2 l0 ∷ s3 l0 ∷ c2 l0 ∷ c3 l0 ∷ s4 l0 ∷ s5 l0 ∷ s6 l0 ∷ c4 l0 ∷ ptB ∷ c1 l1 ∷ s1 l1 ∷ gB ∷ s2 l1 ∷ s3 l1 ∷ c2 l1 ∷ c3 l1 ∷ s4 l1 ∷ s5 l1 ∷ s6 l1 ∷ c4 l1 ∷ ptC ∷ []

-- NON-VACUITY ACROSS BOTH LINKS, at the SHIPPED system `leiosSystemL = rawL ∖ ioES`
-- (definitionally, `LeiosInstance3.sysL≡`): the same run, its wire events hidden
liveL∖ : Σ[ s ∈ List (Event√ (⊤ {0ℓ})) ] traces LIL.leiosSystemL s × Pins s
liveL∖ = sHid , (_ , HideX ioES (proj₂ rawTr)
  ((kp (λ ()) (kp (λ ()) (dp _ (dp _ (kp (λ ()) (kp (λ ()) (kp (λ ()) (dp _
    (dp _ (kp (λ ()) (dp _ (dp _ (kp (λ ()) (kp (λ ()) (dp _ (dp _
    (kp (λ ()) (kp (λ ()) (dp _ (dp _ (kp (λ ()) (dp _ (dp _ (kp (λ ())
    (kp (λ ()) (kp (λ ()) (dp _ (dp _ (kp (λ ()) (kp (λ ()) (kp (λ ()) (dp _
    (dp _ (kp (λ ()) (dp _ (dp _ (kp (λ ()) (kp (λ ()) (dp _ (dp _
    (kp (λ ()) (kp (λ ()) (dp _ (dp _ (kp (λ ()) (dp _ (dp _ (kp (λ ())
    (kp (λ ()) hn))))))))))))))))))))))))))))))))))))))))))))))))))) , s≤s z≤n , refl , refl , s≤s z≤n , s≤s z≤n , refl

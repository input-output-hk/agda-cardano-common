{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE NEGATIVE CONTROL FOR S5: the TX-CLOSURE
-- OFFSET-HASH GUARD is LOAD-BEARING.
--
-- `TxOrigin.txSound` proves `TxSpecT ⊑T nodeP n (nodeLogicL n st₀)` for
-- every `Params`, every `LeiosParams`, every topology and every node: a
-- transaction enters the mempool only if the environment submitted it or
-- this node asked for its hash.  `NodeLogicL.putChecked` earns its deposit
-- with ONE conditional — `⌊ txHash tx ≟ k ⌋`, where `k` is the hash the EB
-- body table names at the entry's own offset, read out of
-- `at? o (ebTxs h)` for the point `h` the client itself requested the tx
-- closure of (spec §5.2, ADR 2026-09-21).  Delete that conditional —
-- `putCheckedBad` below stores whatever the reply carries at a valid offset
-- — and the property FAILS, machine-checked: the node asks for the closure
-- of a point whose table names the transaction `true`, and stores `false`.
--
-- THE WRITE-UP RULE — READ THIS BEFORE QUOTING EITHER RESULT.  `txSound` is
-- ∀-`Params`, ∀-`LeiosParams`, ∀-topology, ∀-node and premise-free.  THE
-- REFUTATION IS NOT: it is at the concrete `leiosLParams` line, at node 0,
-- on one endpoint, over a REDUCED composite (see below).  Never state the
-- two quantifications in one sentence, and never read a system-level break
-- out of the refutation.  Neither result is a validity statement: nothing
-- here says the transaction the node asked for is one it SHOULD have asked
-- for, and nothing in this model ever puts a mempool transaction into a
-- block (see `TxOrigin`'s honest limit (1)).
--
-- WHY THE COMPOSITE IS REDUCED, AND EXACTLY HOW.  The defect lives on the
-- WIRE branch, so the violating trace must contain `apiLP` events —
-- `lnpSendRequestNext`, `lnpRecvBlockTxsOffer`, `lfpSendBlockTxsRequest`,
-- `lfpRecvBlockTxs` — and every `apiLP` channel is inside `apiES`.  Inside
-- `nodeP` those four events would each have to be driven through the
-- twelve-peer prototype bundle's `⦀⋆`, together with the LeiosFetch
-- consumer peer's own `sndmsg`/`rcvmsg` state machine, which this campaign
-- has priced at ~300 NCL and declined four times.  SO THE COMPOSITE HERE IS
-- THE FORGE THREAD AND THE BROKEN NOTIFY CLIENT against the node's five real
-- stores on the same `∥⇘ storeES ⇙` rendezvous, and the statement refuted is
-- `TxSpecT ⊑T <that composite>`, NOT `TxSpecT ⊑T nodeP …`.
--
-- WHY THE FORGE THREAD IS IN IT.  Unlike `BodyOriginBad`, the broken branch
-- cannot be reached from empty stores by the client alone:
-- `NodeLogicL.fetchTxs` BLOCKS at `getBodyEv n (proj₁ q)` before it sends
-- the request, so the node must already HOLD the EB body of the point it was
-- offered.  Rather than seed the body store — which would cost the "from
-- empty stores" claim — the trace is PREFIXED with the two-event forge
-- deposit: at this instance `announcedEB = id`, `ebHash = id` and
-- `rbCert (just true) = nothing`, so `env … envForge ! (just true , just true)`
-- passes `forgeOK`, deposits the body cleanly on `store … stPutBody ! true`,
-- and adds no certificate half.  THE STORES ARE STILL `st₀`: nothing is
-- seeded anywhere.
--
-- WHAT THE PRUNING COSTS, HONESTLY.  A trace of the logic need not survive
-- the bundle: `∥⇘ apiES ⇙` only RESTRICTS, so this refutation does not by
-- itself refute the node-level statement for the broken logic.  What it does
-- refute is the load-bearing half.  `txSound n` is
-- `soundOf n _ (wf-logic n) _`, and `wf-logic` — the `Wf` fact about the node
-- logic alone, which `TxOrigin.soundLogic` turns into `TxSpecT ⊑T <the logic>`
-- with no bundle at all — is the entire content of the theorem; the bundle
-- contributes only `wf-linkBundlesP`, which is vacuous because no peer offers
-- a `store` channel.  The control shows that exact half fails once the guard
-- goes.
--
-- THE PRUNING IS NOT WHAT BREAKS S5, and that is machine-checked TWICE:
-- `txSound-logic-good` proves the SAME composite, the SAME empty stores, with
-- `NodeLogicL.lnClientLoopL` in the client slot, DOES satisfy the
-- specification — through `TxOrigin.soundLogic`, `wf-withStores`,
-- `wf-lnClient` and `oo-forgeL`, the very lemmas `txSound` spends — and
-- `good-refuses` then derives, from those two facts alone, that the violating
-- trace is NOT a trace of the honest composite.  That derived fact IS the
-- mutation test, proved instead of run.
--
-- WHAT THE REFUTATION SPENDS.  Two independent halves:
--
--   * the IMPLEMENTATION half — `bad-tx-fires`: the broken node has the
--     trace ⟨forge of the EB `true`, deposit of that body, long-poll,
--     tx-closure offer for the point `true`, the body read the closure
--     blocks at, the closure request for every offset, delivery of an entry
--     `(0 , false)`, deposit of `false`⟩, all of it FROM EMPTY STORES.  The
--     first seven events are the honest logic's, unchanged; only the eighth
--     is the defect;
--   * the SPECIFICATION half — `noForge`: that same trace is not a trace of
--     `TxSpecT`.  Only the CLOSURE REQUEST mints, and it mints the hashes
--     the table of the requested point names — here the single hash `true`;
--     the delivery mints nothing (minting there would delete the theorem),
--     so when the deposit fires the minted set is `((0 , lo) , true) ∷ []`
--     and the transaction deposited is `false`.  `gate-requested` and
--     `gate-unrequested` pin that the refusal is the OFFSET-HASH MISMATCH and
--     nothing else; `table-pin`, `offsets-pin` and `honest-rejects` pin the
--     shipped-instance facts that make it bite.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.TxOriginBad where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
-- `nothing` IS LISTED: without it the `nothing` clause of `putCheckedBad` below silently
-- becomes a pattern VARIABLE (campaign ledger, gotcha 1), which Agda reports only as a
-- `PatternShadowsConstructor` warning
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (Dir; lo)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import Cardano_network.Net leiosLParams
  using ( Net_Api; Net_Api-≟; Link; store; stPutTx; stPutBody; stGetBody; apiLP; env
        ; envForge
        ; lnpSendRequestNext; lnpRecvBlockAnnouncement; lnpRecvBlockOffer
        ; lnpRecvBlockTxsOffer; lnpRecvVotes
        ; lfpSendBlockTxsRequest; lfpRecvBlockTxs )
open import Cardano_network.Data leiosLParams
  using (Payload; TxBitmap; DecEq-EBPoint; DecEq-TxsRequest)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.TxOrigin as TO

open Params leiosLParams using (Block; EB; EBHash; LSlot; Size; Tx; TxHash; txHash; decTx)
open LeiosP leiosLParams using (LeiosEb; allOffsets)
open LeiosP.LeiosParams leiosLP using (ebTxs)

-- the transaction equality the broken thread's mempool `!`-output needs.  At a CONCRETE
-- instantiation `open Params leiosLParams using (decTx)` does not put the field in
-- instance scope, so it is re-declared.  PRIVATE: an elaboration witness of THIS
-- module's definitions, and the only `DecEq Tx` here — and since `Tx = EB = TxHash =
-- Bool` at this instance, the only `DecEq Bool` too, so nothing can compete with it
-- (ledger gotcha 4).
private
 instance
   DecEq-Tx : DecEq Tx
   DecEq-Tx = decTx

open NL.Generic leiosLParams leiosLLine apiES using (storeES)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using ( StateL; st₀; DecEq-⊤poly; at?; putTxEv; getBodyEv; forgeL
        ; fetchBody; putAllVotes; lnClientLoopL
        ; blockStoreL; ebStore; bodyStore; mempool; voteStore )
-- S5 at this instance: the five parameters `NodeLogicL.Generic` takes, with
-- `VoterId = Node = Fin 3` and the identity voter map
open TO.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using ( Minted; TxSpecT; txGate; originOffer; OriginSpecAt
        ; soundLogic; wf-withStores; wf-lnClient; wf-nP; oo-forgeL; wf-⦀ )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Ret; Skip; pchoice; iter-bind; _>>=_; loop0; _⦀_; _∥⇘_⇙_; _□_
              ; Prefix; Prefix₀; Output; _◁_▷_)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_)
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using (NoRet-Par; NoRet-⦀; NoRet-loop0)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R)

------------------------------------------------------------------------
-- THE BREAK
------------------------------------------------------------------------

-- the node under test: node 0 of the Linear-Leios line, degree 1, its only endpoint
-- being `(link 0 , lo)` — so its store channels are `store fzero lo _`
nA : Fin 3
nA = fzero

-- THE BROKEN DEPOSIT LOOP: `NodeLogicL.putChecked` with the OFFSET-HASH GUARD DELETED.
-- Same offset dispatch — an entry past the end of the table is still skipped — the ONLY
-- difference is that the conditional `◁ ⌊ txHash tx ≟ k ⌋ ▷` is gone, so a neighbour may
-- answer a closure request with ANY transaction at a valid offset and it is stored.  This
-- is the guard the prototype's own entry check stands for (spec §5.2).
putCheckedBad : Fin 3 → EBHash → List (ℕ × Tx) → Proc
putCheckedBad n h []               = Skip
putCheckedBad n h ((o , tx) ∷ es) with at? o (ebTxs h)
... | nothing      = putCheckedBad n h es
... | just (k , _) = putTxEv n ! tx ⟶ putCheckedBad n h es

-- the broken closure fetch: `NodeLogicL.fetchTxs` with `putCheckedBad` in the deposit
-- slot.  The leading body read, the all-offsets request and the ECHOED-POINT check are
-- all untouched — only the per-entry hash check is gone.
fetchTxsBad : Fin 3 → Link → Dir → EBHash × LSlot → Proc
fetchTxsBad n l d q =
  getBodyEv n (proj₁ q) ⟶ (λ _ →
    Output ⦃ DecEq-TxsRequest ⦄ (apiLP l d lfpSendBlockTxsRequest)
      (q , allOffsets leiosLP (proj₁ q))
      (apiLP l d lfpRecvBlockTxs ⟶ (λ { (q′ , es) →
         putCheckedBad n (proj₁ q) es ◁ ⌊ DecEq-EBPoint ._≟_ q′ q ⌋ ▷ Skip })))

-- the broken Notify client's round: `NodeLogicL.lnClientBodyL` with `fetchTxsBad` in the
-- tx-closure-offer branch and the other three branches untouched
lnClientBodyLTxBad : Fin 3 → Link → Dir → Proc
lnClientBodyLTxBad n l d =
  apiLP l d lnpSendRequestNext ⟶₀
    ((apiLP l d lnpRecvBlockAnnouncement ⟶ (λ _ → Skip))
    □ ((apiLP l d lnpRecvBlockOffer    ⟶ fetchBody   n l d)
    □ ((apiLP l d lnpRecvBlockTxsOffer ⟶ fetchTxsBad n l d)
    □  (apiLP l d lnpRecvVotes         ⟶ putAllVotes n))))

-- the broken Notify client thread
lnClientLoopLTxBad : Fin 3 → Link × Dir → Proc
lnClientLoopLTxBad n (l , d) = loop0 (lnClientBodyLTxBad n l d)

-- THE REDUCED CONTROL'S LOGIC — NOT A VARIANT OF `nodeLogicL`, AND NEVER TO BE QUOTED
-- AS ONE.  It is the forge thread and the broken Notify client against the node's five
-- real stores on the same `∥⇘ storeES ⇙` rendezvous, with the other fourteen threads and
-- the whole peer bundle absent.  See the module header for why the forge thread is
-- needed, and for the machine-checked reason nothing depends on the pruning
-- (`txSound-logic-good`, `good-refuses`).
nodeLogicLTxBad : Fin 3 → StateL → Proc
nodeLogicLTxBad n (held , es , bs , ts , vs) =
  (forgeL n ⦀ lnClientLoopLTxBad n (fzero , lo))
    ∥⇘ storeES ⇙
  (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀ (mempool n ts ⦀ voteStore n vs))))

-- THE GOOD COMPOSITE: the very same shape with `NodeLogicL.lnClientLoopL` — the
-- guard-carrying client — in the client slot
nodeLogicLTxGood : Fin 3 → StateL → Proc
nodeLogicLTxGood n (held , es , bs , ts , vs) =
  (forgeL n ⦀ lnClientLoopL n (fzero , lo))
    ∥⇘ storeES ⇙
  (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀ (mempool n ts ⦀ voteStore n vs))))

-- THE PROCESS UNDER TEST, FROM EMPTY STORES.  No seeding anywhere: the body the closure
-- fetch blocks at is FORGED by the first two events of the trace, from `st₀` — the very
-- state `txSound` quantifies over.
badLogic : Proc
badLogic = nodeLogicLTxBad nA st₀

-- … and the honest one at the same empty stores
goodLogic : Proc
goodLogic = nodeLogicLTxGood nA st₀

------------------------------------------------------------------------
-- The shipped-instance facts that make the break bite
------------------------------------------------------------------------

-- THE EB BODY TABLE of the point `true` has exactly one entry, naming the transaction
-- `true` (`LeiosInstanceL.leiosLP`).  With an EMPTY table the closure branch would be
-- vacuous and nothing could be deposited at all.
table-pin : ebTxs true ≡ (true , U.tt) ∷ []
table-pin = refl

-- … so the all-offsets request for that point asks for offset 0 and nothing else
offsets-pin : allOffsets leiosLP true ≡ 0 ∷ []
offsets-pin = refl

-- THE TRANSACTION THE NEIGHBOUR ACTUALLY DELIVERS at offset 0: `false`, which is NOT the
-- transaction the table names there (`txHash` is the identity here)
txBad : Tx
txBad = false

-- … and the transaction that WOULD have matched, for the non-vacuity probe below
txGood : Tx
txGood = true

-- THE HONEST GUARD WOULD HAVE REJECTED IT: `putChecked`'s `⌊ txHash tx ≟ k ⌋` at the
-- delivered `false` against the table's hash `true` computes to `false`, so the honest
-- logic skips the entry.  This is the one conditional `putCheckedBad` deletes.
honest-rejects : ⌊ txHash txBad ≟ true ⌋ ≡ false
honest-rejects = refl

------------------------------------------------------------------------
-- The eight visible events of the bad trace
------------------------------------------------------------------------

-- THE POINT THE NODE IS OFFERED AND ASKS THE CLOSURE OF (`LSlot = ⊤` at this instance,
-- so a point is its hash)
qGood : EBHash × LSlot
qGood = true , U.tt

-- event 1: the environment hands the node a ranking block announcing the EB `true`
-- together with that EB's body.  `forgeOK` passes (`announcedEB = id`, `ebHash = id`) and
-- `rbCert (just true) = nothing`, so the pass is exactly "deposit the body".  Mints
-- nothing for S5 — a forge is not a transaction submission.
evForge : Event√ (⊤ {0ℓ})
evForge = evl (evLabel (Maybe EB × Block) (env fzero lo envForge) (just true , just true))

-- event 2: the forged EB body enters the body store.  S5 does not gate `stPutBody` (that
-- is S1) and does not mint on it either.
evPutBody : Event√ (⊤ {0ℓ})
evPutBody = evl (evLabel EB (store fzero lo stPutBody) true)

-- event 3: the long-poll request that opens a Notify round.  Mints nothing.
evReqNext : Event√ (⊤ {0ℓ})
evReqNext = evl (evLabel U.⊤ (apiLP fzero lo lnpSendRequestNext) U.tt)

-- event 4: the neighbour offers the TX CLOSURE of the point `true`.  An OFFER mints
-- nothing — only the node's own REQUEST does, which is what makes S5 about the node's own
-- asking.
evOffer : Event√ (⊤ {0ℓ})
evOffer = evl (evLabel (EBHash × LSlot) (apiLP fzero lo lnpRecvBlockTxsOffer) qGood)

-- event 5: the body read `fetchTxs` BLOCKS at before it will request a closure — served
-- by the body store out of the body event 2 deposited
evGetBody : Event√ (⊤ {0ℓ})
evGetBody = evl (evLabel EB (store fzero lo (stGetBody true)) true)

-- event 6: THE CLOSURE REQUEST, and the one minting event of the trace: it mints every
-- hash the EB body table of `true` names, i.e. the single hash `true`
evSendReq : Event√ (⊤ {0ℓ})
evSendReq =
  evl (evLabel ((EBHash × LSlot) × TxBitmap)
               (apiLP fzero lo lfpSendBlockTxsRequest) (qGood , 0 ∷ []))

-- event 7: the neighbour echoes the point — so the echoed-point check passes — but puts
-- the WRONG transaction at offset 0.  The delivery mints nothing.
evRecvTxs : Event√ (⊤ {0ℓ})
evRecvTxs =
  evl (evLabel ((EBHash × LSlot) × List (ℕ × Tx))
               (apiLP fzero lo lfpRecvBlockTxs) (qGood , (0 , txBad) ∷ []))

-- event 8: THE UNSOLICITED DEPOSIT — a transaction the node was neither handed nor asked
-- for enters the mempool
evPutTx : Event√ (⊤ {0ℓ})
evPutTx = evl (evLabel Tx (store fzero lo stPutTx) txBad)

-- THE WHOLE BAD TRACE, named once so the implementation and specification halves, and the
-- derived mutation test, all quote the same list
badTrace : List (Event√ (⊤ {0ℓ}))
badTrace = evForge ∷ evPutBody ∷ evReqNext ∷ evOffer ∷ evGetBody
         ∷ evSendReq ∷ evRecvTxs ∷ evPutTx ∷ []

-- THE MINTED SET THE CLOSURE REQUEST LEAVES BEHIND.  A mint carries the endpoint the
-- deposit it licenses is made at: node `nA` has degree 1, so the endpoint it asked at is
-- already its own home endpoint and `homeAt (fzero , lo)` IS `(fzero , lo)`.
msMint : Minted
msMint = ((fzero , lo) , true) ∷ []

------------------------------------------------------------------------
-- The nine steps (eight visible, one τ)
--
-- Each is stated as "there is a state such that …", so the target of one step is
-- `proj₁` of it and the next step's source (`BodyOriginBad`'s shape).  The four `apiLP`
-- events are OUTSIDE `storeES`, so the store group stays put; the `env` and `store`
-- events ARE in `storeES`, so a thread and a store synchronise.  The ONE τ is the body
-- store's loop-back after the deposit, without which it is not back at its read menu
-- when event 5 asks it for the body.
------------------------------------------------------------------------

-- STEP 1.  The forge: the forge thread with the ranking-block store.
step₁ : Σ[ P₁ ∈ Proc ] (badLogic ─[ ev evForge ]─► P₁)
step₁ = _ ,
  Par-sync _ _ _ _ _
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)

-- STEP 2.  The forged body enters the body store, the third of the five stores.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ ev evPutBody ]─► P₂)
step₂ = _ ,
  Par-sync _ _ _ _ _
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      refl) refl)

-- STEP 3.  THE ONE τ: the body store's loop-back, which puts it back at the menu that
-- offers `stGetBody true`.
step₃ : Σ[ P₃ ∈ Proc ] (proj₁ step₂ ─[ τ ]─► P₃)
step₃ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _ (sSil refl))))

-- STEP 4.  The long-poll request, the client alone.
step₄ : Σ[ P₄ ∈ Proc ] (proj₁ step₃ ─[ ev evReqNext ]─► P₄)
step₄ = _ ,
  Par-soloL _ _ _ _ (λ ()) (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl) refl

-- STEP 5.  The tx-closure offer arrives, selecting the THIRD branch of the four-way `□`.
step₅ : Σ[ P₅ ∈ Proc ] (proj₁ step₄ ─[ ev evOffer ]─► P₅)
step₅ = _ ,
  Par-soloL _ _ _ _ (λ ()) (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl) refl

-- STEP 6.  The body read the closure fetch blocks at, served by the body store.
step₆ : Σ[ P₆ ∈ Proc ] (proj₁ step₅ ─[ ev evGetBody ]─► P₆)
step₆ = _ ,
  Par-sync _ _ _ _ _
    (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      refl) refl)

-- STEP 7.  THE CLOSURE REQUEST: the node asks for every offset of the table of `true`.
-- This is the mint.
step₇ : Σ[ P₇ ∈ Proc ] (proj₁ step₆ ─[ ev evSendReq ]─► P₇)
step₇ = _ ,
  Par-soloL _ _ _ _ (λ ()) (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl) refl

-- STEP 8.  The neighbour echoes the point and delivers the WRONG transaction at offset 0.
step₈ : Σ[ P₈ ∈ Proc ] (proj₁ step₇ ─[ ev evRecvTxs ]─► P₈)
step₈ = _ ,
  Par-soloL _ _ _ _ (λ ()) (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl) refl

-- STEP 9.  THE UNSOLICITED DEPOSIT: the broken client with the mempool, which accepts
-- ANY transaction.  Fourth of the five stores.
step₉ : Σ[ P₉ ∈ Proc ] (proj₁ step₈ ─[ ev evPutTx ]─► P₉)
step₉ = _ ,
  Par-sync _ _ _ _ _
    (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      refl) refl) refl)

-- THE BROKEN NODE STORES A TRANSACTION IT NEVER ASKED FOR: it requests the closure of a
-- point whose table names `true` and deposits `false`, from empty stores
bad-tx-fires : traces badLogic badTrace
bad-tx-fires =
  _ , ⟹-ev (proj₂ step₁) (⟹-ev (proj₂ step₂) (⟹-τ (proj₂ step₃)
        (⟹-ev (proj₂ step₄) (⟹-ev (proj₂ step₅) (⟹-ev (proj₂ step₆)
          (⟹-ev (proj₂ step₇) (⟹-ev (proj₂ step₈) (⟹-ev (proj₂ step₉) ⟹-refl))))))))

------------------------------------------------------------------------
-- The two states `TxSpecT` alternates between
------------------------------------------------------------------------

-- the tree type the spec's `loop` iterates over
Tree : Set → Set₁
Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

-- `loop`'s state-threading continuation: hand the new minted set back to `iter`
κ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
κ ms = Ret (inj₁ ms)

-- the `iter` step `TxSpecT`'s `loop` is built from
StepT : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
StepT ms = pchoice (originOffer ms) >>= κ

-- the spec's LOOP-BACK state, reached by any visible event.  The MENU state is the
-- carrier's own `OriginSpecAt`; this one has to be re-formed because `Origin`'s copy
-- is `private`, which is also why `Tree`/`κ`/`StepT` above stay.
ST : Minted → Proc
ST ms = iter-bind (Ret ms >>= κ) StepT

------------------------------------------------------------------------
-- The specification half: the bad trace is refused
------------------------------------------------------------------------

-- from the loop-back edge the ONLY move is the `sil` back to the menu, so any run of a
-- NON-EMPTY trace from `ST ms` is a run of that trace from `OriginSpecAt ms`
backEdge : ∀ {ms e s q} → ST ms ⟹⟨ e ∷ s ⟩ q → Σ[ q′ ∈ Proc ] (OriginSpecAt ms ⟹⟨ e ∷ s ⟩ q′)
backEdge (⟹-τ (sSil refl) rest) = _ , rest
backEdge (⟹-τ (sTau eq _) _)    = case eq of λ ()
backEdge (⟹-ev (sRet eq) _)     = case eq of λ ()
backEdge (⟹-ev (sVis eq _) _)   = case eq of λ ()

-- NON-VACUITY, PINPOINTED — the transaction the table DID name is licensed outright at
-- the very same minted set, at the very same channel
gate-requested : txGate msMint (Tx , store fzero lo stPutTx) txGood ≡ true
gate-requested = refl

-- … and the transaction it did NOT name is not.  So what refuses the deposit is the
-- OFFSET-HASH MISMATCH and nothing else — exactly the conditional `putCheckedBad` deleted.
gate-unrequested : txGate msMint (Tx , store fzero lo stPutTx) txBad ≡ false
gate-unrequested = refl

-- THE GATE.  The request minted `true`, the delivery minted nothing, and the transaction
-- deposited is `false`, so `txGate msMint _ false` computes to `false`: the deposit is not
-- offered and the spec's map is definitionally `nothing`.  The menu has no τ either,
-- hence three clauses.
noPutTx : ∀ {q} → ¬ (OriginSpecAt msMint ⟹⟨ evPutTx ∷ [] ⟩ q)
noPutTx (⟹-τ (sSil eq) _) = case eq of λ ()
noPutTx (⟹-τ (sTau refl ()) _)
noPutTx (⟹-ev (sVis refl ()) _)

-- the DELIVERY mints nothing: minting there would licence whatever a reply happens to
-- carry and delete the theorem
noRecvTxs : ∀ {q} → ¬ (OriginSpecAt msMint ⟹⟨ evRecvTxs ∷ evPutTx ∷ [] ⟩ q)
noRecvTxs (⟹-τ (sSil eq) _) = case eq of λ ()
noRecvTxs (⟹-τ (sTau refl ()) _)
noRecvTxs (⟹-ev (sVis refl refl) rest) = noPutTx (proj₂ (backEdge {ms = msMint} rest))

-- the CLOSURE REQUEST is the one minting event of the trace, and it mints `true` — not
-- `false`
noSendReq : ∀ {q} → ¬ (OriginSpecAt []
                         ⟹⟨ evSendReq ∷ evRecvTxs ∷ evPutTx ∷ [] ⟩ q)
noSendReq (⟹-τ (sSil eq) _) = case eq of λ ()
noSendReq (⟹-τ (sTau refl ()) _)
noSendReq (⟹-ev (sVis refl refl) rest) = noRecvTxs (proj₂ (backEdge {ms = msMint} rest))

-- a body READ mints nothing
noGetBody : ∀ {q} → ¬ (OriginSpecAt []
                         ⟹⟨ evGetBody ∷ evSendReq ∷ evRecvTxs ∷ evPutTx ∷ [] ⟩ q)
noGetBody (⟹-τ (sSil eq) _) = case eq of λ ()
noGetBody (⟹-τ (sTau refl ()) _)
noGetBody (⟹-ev (sVis refl refl) rest) = noSendReq (proj₂ (backEdge {ms = []} rest))

-- an OFFER received mints nothing: what licences a deposit is the node's own asking
noOffer : ∀ {q} → ¬ (OriginSpecAt []
                       ⟹⟨ evOffer ∷ evGetBody ∷ evSendReq ∷ evRecvTxs ∷ evPutTx ∷ [] ⟩ q)
noOffer (⟹-τ (sSil eq) _) = case eq of λ ()
noOffer (⟹-τ (sTau refl ()) _)
noOffer (⟹-ev (sVis refl refl) rest) = noGetBody (proj₂ (backEdge {ms = []} rest))

-- the long poll mints nothing
noReqNext : ∀ {q} → ¬ (OriginSpecAt []
                         ⟹⟨ evReqNext ∷ evOffer ∷ evGetBody ∷ evSendReq ∷ evRecvTxs
                            ∷ evPutTx ∷ [] ⟩ q)
noReqNext (⟹-τ (sSil eq) _) = case eq of λ ()
noReqNext (⟹-τ (sTau refl ()) _)
noReqNext (⟹-ev (sVis refl refl) rest) = noOffer (proj₂ (backEdge {ms = []} rest))

-- an EB-BODY deposit mints nothing for S5 — that channel is S1's business
noPutBody : ∀ {q} → ¬ (OriginSpecAt []
                         ⟹⟨ evPutBody ∷ evReqNext ∷ evOffer ∷ evGetBody ∷ evSendReq
                            ∷ evRecvTxs ∷ evPutTx ∷ [] ⟩ q)
noPutBody (⟹-τ (sSil eq) _) = case eq of λ ()
noPutBody (⟹-τ (sTau refl ()) _)
noPutBody (⟹-ev (sVis refl refl) rest) = noReqNext (proj₂ (backEdge {ms = []} rest))

-- THE WHOLE BAD TRACE IS REFUSED, from the empty minted set the specification starts in.
-- A FORGE mints nothing either: S5's `env` mint is `envSubmit`, not `envForge`.
noForge : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ badTrace ⟩ q)
noForge (⟹-τ (sSil eq) _) = case eq of λ ()
noForge (⟹-τ (sTau refl ()) _)
noForge (⟹-ev (sVis refl refl) rest) = noPutBody (proj₂ (backEdge {ms = []} rest))

------------------------------------------------------------------------
-- THE NEGATIVE CONTROL
------------------------------------------------------------------------

-- the transaction-origin property over the BROKEN logic: exactly `TxOrigin.TxSound`'s
-- specification and order, but with `putCheckedBad` in the deposit slot, over the
-- REDUCED composite of the module header and from the EMPTY stores
TxSound-node-Bad : Set₁
TxSound-node-Bad = TxSpecT ⊑T badLogic

-- THE REFUTATION: dropping the offset-hash guard BREAKS transaction origin.  This ONE
-- node, on this ONE instance, running the broken Notify client from empty stores over the
-- REDUCED composite, has a trace the specification forbids, so the trace refinement
-- cannot hold — the shipped theorem is not vacuous and `putChecked`'s guard is
-- load-bearing.
--
-- LEVEL: node LOGIC, not the node composite — see "WHY THE COMPOSITE IS REDUCED" and
-- "WHAT THE PRUNING COSTS, HONESTLY" in the module header.  SCOPE: this instance, this
-- node, this endpoint.  WRITE-UP RULE: never pair this with `txSound`'s "∀ Params".
txSound-node-FAILS : ¬ TxSound-node-Bad
txSound-node-FAILS h = noForge (proj₂ (h _ bad-tx-fires))

-- THE CONTROL'S OWN CONTROL: the SAME composite, the SAME empty stores, with
-- `NodeLogicL.lnClientLoopL` — the guard-carrying client — in the client slot DOES
-- satisfy the specification, assembled by `TxOrigin.soundLogic` and `wf-withStores` from
-- `oo-forgeL` and `wf-lnClient`, the very leaves `txSound` spends.  So what fails above
-- is the deleted guard, not the pruning of the bundle and the other threads.
txSound-logic-good : TxSpecT ⊑T goodLogic
txSound-logic-good =
  soundLogic goodLogic
    (wf-withStores (wf-⦀ (wf-nP (oo-forgeL nA))
                         (wf-lnClient nA (fzero , lo) (here refl))))
    (NoRet-Par storeES (λ _ _ → tt) (NoRet-⦀ NoRet-loop0))

-- THE MUTATION TEST, PROVED RATHER THAN RUN.  A scratch copy with the honest guard
-- restored, shown to go red, would check that the violating trace depends on the break;
-- the two facts above already give that outright, and machine-check it: every trace of
-- the honest composite is a trace of the specification (`txSound-logic-good`) and this
-- one is not (`noForge`), so the honest composite does not have it.
good-refuses : ¬ traces goodLogic badTrace
good-refuses h = noForge (proj₂ (txSound-logic-good _ h))

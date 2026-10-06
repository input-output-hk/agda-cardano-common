{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE NEGATIVE CONTROL FOR S1: the
-- REQUESTED-POINT GUARD is LOAD-BEARING.
--
-- `BodyOrigin.bodySound` proves `BodySpecT ⊑T nodeP n (nodeLogicL n st₀)`
-- for every `Params`, every `LeiosParams`, every topology and every node: an
-- EB body enters the body store only if this node forged it or asked for the
-- point it matches.  `NodeLogicL.fetchBody` earns its deposit with ONE
-- conditional — `⌊ ebHash eb ≟ proj₁ q ⌋`, against the point the client
-- itself sent on `lfpSendBlockRequest`, because the prototype's
-- `MsgLeiosBlock` carries no point of its own (spec §2.2, §3 "wire checks").
-- Delete that conditional — `fetchBad` below stores whatever arrives — and
-- the property FAILS, machine-checked: the node asks for `true` and stores
-- `false`.
--
-- THE WRITE-UP RULE — READ THIS BEFORE QUOTING EITHER RESULT.  `bodySound`
-- is ∀-`Params`, ∀-`LeiosParams`, ∀-topology, ∀-node and premise-free.  THE
-- REFUTATION IS NOT: it is at the concrete `leiosLParams` line, at node 0,
-- on one endpoint, over a REDUCED composite (see below).  Never state the
-- two quantifications in one sentence, and never read a system-level break
-- out of the refutation.  Neither result is a validity statement: nothing
-- here says the body the node asked for is a body it SHOULD have asked for.
--
-- WHY THE COMPOSITE IS REDUCED, AND EXACTLY HOW.  The defect lives on the
-- WIRE branch, so the violating trace must contain `apiLP` events —
-- `lnpSendRequestNext`, `lnpRecvBlockOffer`, `lfpSendBlockRequest`,
-- `lfpRecvBlock` — and every `apiLP` channel is inside `apiES`.  Inside
-- `nodeP` those four events would each have to be driven through the
-- twelve-peer prototype bundle's `⦀⋆`, together with the LeiosFetch
-- consumer peer's own `sndmsg`/`rcvmsg` state machine: the Task-1 pricing
-- datum for bundle-level navigation is ~300 NCL, and this campaign has
-- declined that cost three times already.  SO THE COMPOSITE HERE IS THE NODE
-- LOGIC WITHOUT ITS PEER BUNDLE — the broken Notify client against the
-- node's five real stores on the same `∥⇘ storeES ⇙` rendezvous — and the
-- statement refuted is `BodySpecT ⊑T <that composite>`, NOT
-- `BodySpecT ⊑T nodeP …`.
--
-- WHAT THAT COSTS, HONESTLY.  A trace of the logic need not survive the
-- bundle: `∥⇘ apiES ⇙` only RESTRICTS, so this refutation does not by itself
-- refute the node-level statement for the broken logic.  What it does refute
-- is the load-bearing half.  `bodySound n` is
-- `soundOf n _ (wf-logic n) _`, and `wf-logic` — the `Wf` fact about the
-- node logic alone, which `BodyOrigin.soundLogic` turns into
-- `BodySpecT ⊑T <the logic>` with no bundle at all — is the entire content
-- of the theorem; the bundle contributes only `wf-linkBundlesP`, which is
-- vacuous because no peer offers a `store` channel.  The control shows that
-- exact half fails once the guard goes.
--
-- THE PRUNING IS NOT WHAT BREAKS S1, and that is machine-checked:
-- `bodySound-logic-good` at the bottom proves the SAME composite, the SAME
-- empty stores, with `NodeLogicL.lnClientLoopL` in the thread slot, DOES
-- satisfy the specification — through `BodyOrigin.soundLogic`,
-- `wf-withStores` and `wf-lnClient`, the very lemmas `bodySound` spends.
--
-- WHAT THE REFUTATION SPENDS.  Two independent halves:
--
--   * the IMPLEMENTATION half — `bad-body-fires`: the broken node has the
--     trace ⟨long-poll, body offer for the point `true`, request for `true`,
--     delivery of the body `false`, deposit of `false`⟩.  The first four
--     events are the honest client's, unchanged; only the fifth is the
--     defect, and it happens FROM EMPTY STORES (no seeding at all);
--   * the SPECIFICATION half — `noReqNext`: that same trace is not a trace
--     of `BodySpecT`.  Only the REQUEST mints, and it mints `true`; the
--     delivery mints nothing (minting there would delete the theorem), so
--     when the deposit fires the minted set is `true ∷ []` and the body
--     deposited is `false`.  `gate-requested` and `gate-unrequested` pin
--     that the refusal is the HASH MISMATCH and nothing else.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.BodyOriginBad where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (Dir; lo)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import Cardano_network.Net leiosLParams
  using ( Net_Api; Net_Api-≟; Link; store; stPutBody; apiLP
        ; lnpSendRequestNext; lnpRecvBlockAnnouncement; lnpRecvBlockOffer
        ; lnpRecvBlockTxsOffer; lnpRecvVotes; lfpSendBlockRequest; lfpRecvBlock )
open import Cardano_network.Data leiosLParams
  using (Payload; DecEq-EBPoint)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.BodyOrigin as BO

open Params leiosLParams using (Block; EB; EBHash; LSlot; Size; decEB)
open LeiosP leiosLParams using (LeiosEb)

-- the EB equality the broken thread's body `!`-output needs.  At a CONCRETE
-- instantiation `open Params leiosLParams using (decEB)` does not put the field in
-- instance scope, so it is re-declared.  PRIVATE: an elaboration witness of THIS
-- module's definitions, and the only `DecEq EB` here, so nothing can compete with it
-- (ledger gotcha 4 — at this instance `EB = EBHash = Tx = Bool`).
private
 instance
   DecEq-EB : DecEq EB
   DecEq-EB = decEB

open NL.Generic leiosLParams leiosLLine apiES using (storeES)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using ( StateL; st₀; DecEq-⊤poly; putBodyEv; fetchBody; fetchTxs; putAllVotes
        ; lnClientLoopL; blockStoreL; ebStore; bodyStore; mempool; voteStore )
-- S1 at this instance: the five parameters `NodeLogicL.Generic` takes, with
-- `VoterId = Node = Fin 3` and the identity voter map
open BO.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using ( Minted; BodySpecT; bodyGate; originOffer; OriginSpecAt
        ; soundLogic; wf-withStores; wf-lnClient )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Ret; Skip; pchoice; iter-bind; _>>=_; loop0; _⦀_; _∥⇘_⇙_; _□_; Prefix; Prefix₀; Output)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_)
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using (NoRet-Par; NoRet-loop0)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloL; Par-soloR)

------------------------------------------------------------------------
-- THE BREAK
------------------------------------------------------------------------

-- the node under test: node 0 of the Linear-Leios line, degree 1, its only endpoint
-- being `(link 0 , lo)` — so its store channels are `store fzero lo _`
nA : Fin 3
nA = fzero

-- THE BROKEN FETCH: `NodeLogicL.fetchBody` with the wire guard DELETED.  Same request,
-- same reply channel, same deposit — the ONLY difference is that the conditional
-- `◁ ⌊ ebHash eb ≟ proj₁ q ⌋ ▷ Skip` is gone, so a neighbour may hand over ANY body
-- against the offer and it is stored.  This is the guard the prototype's own
-- "MsgLeiosBlock hash mismatch" check stands for (spec §3).
fetchBad : Fin 3 → Link → Dir → (EBHash × LSlot) × Size → Proc
fetchBad n l d (q , _) =
  Output ⦃ DecEq-EBPoint ⦄ (apiLP l d lfpSendBlockRequest) q
    (apiLP l d lfpRecvBlock ⟶ (λ eb → putBodyEv n ! eb ⟶ Skip))

-- the broken Notify client's round: `NodeLogicL.lnClientBodyL` with `fetchBad` in the
-- body-offer branch and the other three branches untouched
lnClientBodyLBodyBad : Fin 3 → Link → Dir → Proc
lnClientBodyLBodyBad n l d =
  apiLP l d lnpSendRequestNext ⟶₀
    ((apiLP l d lnpRecvBlockAnnouncement ⟶ (λ _ → Skip))
    □ ((apiLP l d lnpRecvBlockOffer    ⟶ fetchBad n l d)
    □ ((apiLP l d lnpRecvBlockTxsOffer ⟶ fetchTxs  n l d)
    □  (apiLP l d lnpRecvVotes         ⟶ putAllVotes n))))

-- the broken Notify client thread
lnClientLoopLBodyBad : Fin 3 → Link × Dir → Proc
lnClientLoopLBodyBad n (l , d) = loop0 (lnClientBodyLBodyBad n l d)

-- THE REDUCED CONTROL'S LOGIC — NOT A VARIANT OF `nodeLogicL`, AND NEVER TO BE QUOTED
-- AS ONE.  It is the broken Notify client against the node's five real stores on the
-- same `∥⇘ storeES ⇙` rendezvous, with the other fifteen threads and the whole peer
-- bundle absent.  See the module header for why, and for the machine-checked reason
-- nothing depends on it (`bodySound-logic-good`).
nodeLogicLBodyBad : Fin 3 → StateL → Proc
nodeLogicLBodyBad n (held , es , bs , ts , vs) =
  lnClientLoopLBodyBad n (fzero , lo)
    ∥⇘ storeES ⇙
  (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀ (mempool n ts ⦀ voteStore n vs))))

-- THE GOOD COMPOSITE: the very same shape with `NodeLogicL.lnClientLoopL` — the
-- guard-carrying client — in the thread slot
nodeLogicLBodyGood : Fin 3 → StateL → Proc
nodeLogicLBodyGood n (held , es , bs , ts , vs) =
  lnClientLoopL n (fzero , lo)
    ∥⇘ storeES ⇙
  (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀ (mempool n ts ⦀ voteStore n vs))))

-- THE PROCESS UNDER TEST, FROM EMPTY STORES.  No seeding is needed at all: the defect
-- is on the wire path, so the violation is reachable from `st₀` — the very state
-- `bodySound` quantifies over.
badLogic : Proc
badLogic = nodeLogicLBodyBad nA st₀

------------------------------------------------------------------------
-- The five visible events of the bad trace
------------------------------------------------------------------------

-- THE POINT THE NODE ASKS FOR (`LSlot = ⊤` at this instance, so a point is its hash)
qGood : EBHash × LSlot
qGood = true , U.tt

-- the offer that names it (`Size = ⊤`)
offerGood : (EBHash × LSlot) × Size
offerGood = qGood , U.tt

-- THE BODY THE NEIGHBOUR ACTUALLY DELIVERS: `false`, which is NOT the body the node
-- asked for (`ebHash` is the identity here, so `ebHash false ≢ true`)
ebBad : EB
ebBad = false

-- … and the body that WOULD have matched, for the non-vacuity probe below
ebGood : EB
ebGood = true

-- event 1: the long-poll request that opens a Notify round.  Mints nothing.
evReqNext : Event√ (⊤ {0ℓ})
evReqNext = evl (evLabel U.⊤ (apiLP fzero lo lnpSendRequestNext) U.tt)

-- event 2: the neighbour offers the body at point `true`.  An OFFER mints nothing —
-- only the node's own REQUEST does, which is what makes S1 about the node's own asking.
evOffer : Event√ (⊤ {0ℓ})
evOffer = evl (evLabel ((EBHash × LSlot) × Size) (apiLP fzero lo lnpRecvBlockOffer) offerGood)

-- event 3: THE REQUEST, and the one minting event of the trace: it mints `true`
evSendReq : Event√ (⊤ {0ℓ})
evSendReq = evl (evLabel (EBHash × LSlot) (apiLP fzero lo lfpSendBlockRequest) qGood)

-- event 4: the neighbour delivers the WRONG body.  `MsgLFPBlock` carries no point, so
-- nothing on the wire contradicts it — and the delivery mints nothing.
evRecvBlock : Event√ (⊤ {0ℓ})
evRecvBlock = evl (evLabel EB (apiLP fzero lo lfpRecvBlock) ebBad)

-- event 5: THE UNSOLICITED DEPOSIT — a body the node neither forged nor asked for
evPutBody : Event√ (⊤ {0ℓ})
evPutBody = evl (evLabel EB (store fzero lo stPutBody) ebBad)

-- THE MINTED SET THE REQUEST LEAVES BEHIND.  Since the re-keying, a mint carries the
-- endpoint the deposit it licenses is made at: node `nA` has degree 1, so the endpoint it
-- asked at is already its own home endpoint and `homeAt (fzero , lo)` IS `(fzero , lo)`.
msReq : Minted
msReq = ((fzero , lo) , true) ∷ []

------------------------------------------------------------------------
-- The five steps
--
-- Each is stated as "there is a state such that …", so the target of one step is
-- `proj₁` of it and the next step's source (`VoteSoundBad`'s shape).  The four `apiLP`
-- events are OUTSIDE `storeES`, so the store group stays put (`Par-soloL`); the
-- deposit IS in `storeES`, so the thread and the store group synchronise.  There is no
-- τ anywhere in between: `⟶₀`, `□`, `Output` and `⟶` all step straight on.
------------------------------------------------------------------------

-- STEP 1.  The long-poll request, the client alone.
step₁ : Σ[ P₁ ∈ Proc ] (badLogic ─[ ev evReqNext ]─► P₁)
step₁ = _ , Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl

-- STEP 2.  The body offer arrives, selecting the second branch of the four-way `□`.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ ev evOffer ]─► P₂)
step₂ = _ , Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl

-- STEP 3.  THE REQUEST: the node asks for the point `true`.  This is the mint.
step₃ : Σ[ P₃ ∈ Proc ] (proj₁ step₂ ─[ ev evSendReq ]─► P₃)
step₃ = _ , Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl

-- STEP 4.  The neighbour delivers the body `false` instead.
step₄ : Σ[ P₄ ∈ Proc ] (proj₁ step₃ ─[ ev evRecvBlock ]─► P₄)
step₄ = _ , Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl

-- STEP 5.  THE UNSOLICITED DEPOSIT: the broken client with the EB-body store, which
-- accepts ANY body.  Third of the five stores.
step₅ : Σ[ P₅ ∈ Proc ] (proj₁ step₄ ─[ ev evPutBody ]─► P₅)
step₅ = _ ,
  Par-sync _ _ _ _ _
    (sVis refl refl)
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      refl) refl)

-- THE BROKEN NODE STORES A BODY IT NEVER ASKED FOR: it requests the point `true` and
-- deposits the body `false`
bad-body-fires : traces badLogic
                   (evReqNext ∷ evOffer ∷ evSendReq ∷ evRecvBlock ∷ evPutBody ∷ [])
bad-body-fires =
  _ , ⟹-ev (proj₂ step₁) (⟹-ev (proj₂ step₂) (⟹-ev (proj₂ step₃)
        (⟹-ev (proj₂ step₄) (⟹-ev (proj₂ step₅) ⟹-refl))))

------------------------------------------------------------------------
-- The two states `BodySpecT` alternates between
------------------------------------------------------------------------

-- the tree type the spec's `loop` iterates over
Tree : Set → Set₁
Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

-- `loop`'s state-threading continuation: hand the new minted set back to `iter`
κ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
κ ms = Ret (inj₁ ms)

-- the `iter` step `BodySpecT`'s `loop` is built from
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

-- NON-VACUITY, PINPOINTED — the body the node DID ask for is licensed outright at the
-- very same minted set, at the very same channel
gate-requested : bodyGate msReq (EB , store fzero lo stPutBody) ebGood ≡ true
gate-requested = refl

-- … and the body it did NOT ask for is not.  So what refuses the deposit is the HASH
-- MISMATCH and nothing else — exactly the conditional `fetchBad` deleted.
gate-unrequested : bodyGate msReq (EB , store fzero lo stPutBody) ebBad ≡ false
gate-unrequested = refl

-- THE GATE.  The request minted `true`, the delivery minted nothing, and the body
-- deposited is `false`, so `bodyGate msReq _ false` computes to `false`: the
-- deposit is not offered and the spec's map is definitionally `nothing`.  The menu has
-- no τ either, hence three clauses.
noPut : ∀ {q} → ¬ (OriginSpecAt msReq ⟹⟨ evPutBody ∷ [] ⟩ q)
noPut (⟹-τ (sSil eq) _) = case eq of λ ()
noPut (⟹-τ (sTau refl ()) _)
noPut (⟹-ev (sVis refl ()) _)

-- the DELIVERY mints nothing: minting there would licence any body at all and delete
-- the theorem
noRecv : ∀ {q} → ¬ (OriginSpecAt msReq ⟹⟨ evRecvBlock ∷ evPutBody ∷ [] ⟩ q)
noRecv (⟹-τ (sSil eq) _) = case eq of λ ()
noRecv (⟹-τ (sTau refl ()) _)
noRecv (⟹-ev (sVis refl refl) rest) = noPut (proj₂ (backEdge {ms = msReq} rest))

-- the REQUEST is the one minting event, and it mints `true` — not `false`
noSend : ∀ {q} → ¬ (OriginSpecAt []
                      ⟹⟨ evSendReq ∷ evRecvBlock ∷ evPutBody ∷ [] ⟩ q)
noSend (⟹-τ (sSil eq) _) = case eq of λ ()
noSend (⟹-τ (sTau refl ()) _)
noSend (⟹-ev (sVis refl refl) rest) = noRecv (proj₂ (backEdge {ms = msReq} rest))

-- an OFFER received mints nothing: what licences a deposit is the node's own asking
noOffer : ∀ {q} → ¬ (OriginSpecAt []
                       ⟹⟨ evOffer ∷ evSendReq ∷ evRecvBlock ∷ evPutBody ∷ [] ⟩ q)
noOffer (⟹-τ (sSil eq) _) = case eq of λ ()
noOffer (⟹-τ (sTau refl ()) _)
noOffer (⟹-ev (sVis refl refl) rest) = noSend (proj₂ (backEdge {ms = []} rest))

-- THE WHOLE BAD TRACE IS REFUSED, from the empty minted set the specification starts in
noReqNext : ∀ {q} → ¬ (OriginSpecAt []
                         ⟹⟨ evReqNext ∷ evOffer ∷ evSendReq ∷ evRecvBlock
                            ∷ evPutBody ∷ [] ⟩ q)
noReqNext (⟹-τ (sSil eq) _) = case eq of λ ()
noReqNext (⟹-τ (sTau refl ()) _)
noReqNext (⟹-ev (sVis refl refl) rest) = noOffer (proj₂ (backEdge {ms = []} rest))

------------------------------------------------------------------------
-- THE NEGATIVE CONTROL
------------------------------------------------------------------------

-- the body-origin property over the BROKEN logic: exactly `BodyOrigin.BodySound`'s
-- specification and order, but with `fetchBad` in the body-offer branch, over the
-- REDUCED composite of the module header and from the EMPTY stores
BodySound-node-Bad : Set₁
BodySound-node-Bad = BodySpecT ⊑T badLogic

-- THE REFUTATION: dropping the requested-point guard BREAKS body origin.  This ONE
-- node, on this ONE instance, running the broken Notify client from empty stores over
-- the REDUCED composite, has a trace the specification forbids, so the trace refinement
-- cannot hold — the shipped theorem is not vacuous and the wire guard is load-bearing.
--
-- LEVEL: node LOGIC, not the node composite — see "WHY THE COMPOSITE IS REDUCED" and
-- "WHAT THAT COSTS, HONESTLY" in the module header.  SCOPE: this instance, this node,
-- this endpoint.  WRITE-UP RULE: never pair this with `bodySound`'s "∀ Params".
bodySound-node-FAILS : ¬ BodySound-node-Bad
bodySound-node-FAILS h = noReqNext (proj₂ (h _ bad-body-fires))

-- THE CONTROL'S OWN CONTROL: the SAME composite, the SAME empty stores, with
-- `NodeLogicL.lnClientLoopL` — the guard-carrying client — in the thread slot DOES
-- satisfy the specification, assembled by `BodyOrigin.soundLogic` and `wf-withStores`
-- from `wf-lnClient`, the very leaf `bodySound` spends.  So what fails above is the
-- deleted guard, not the pruning of the bundle and the other threads.
bodySound-logic-good : BodySpecT ⊑T nodeLogicLBodyGood nA st₀
bodySound-logic-good =
  soundLogic (nodeLogicLBodyGood nA st₀)
    (wf-withStores (wf-lnClient nA (fzero , lo) (here refl)))
    (NoRet-Par storeES (λ _ _ → tt) NoRet-loop0)

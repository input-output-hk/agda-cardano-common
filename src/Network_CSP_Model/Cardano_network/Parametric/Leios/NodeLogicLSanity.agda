{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE LIVENESS PROBES FOR THE ENVIRONMENT ROUTES
-- of `NodeLogicL`: the certificate-RB forge and `submit` really do take their
-- first event INSIDE THE FULL `nodeLogicL`.
--
-- WHAT THIS ANSWERS.  `NodeLogic.storeSet` puts EVERY `env` channel in the
-- rendezvous set `storeES`, and under `∥⇘ storeES ⇙` a synchronised event
-- fires only when BOTH operands offer it, so an `env` channel no store serves
-- blocks its thread at the first event.  `submit` was in exactly that state as
-- originally shipped — `memStep` offered no `env` channel at all, so the node
-- had no environment route into its mempool — and `memStep` gained one
-- pure-rendezvous `envSubmit` arm.
--
-- THE CERTIFICATE-RB FORGE HAS NO CHANNEL OF ITS OWN any more.  An earlier
-- revision gave it `env … envForgeCert` and a `forgeCert` thread; that tag is
-- deleted and the route is merged into `forgeL`/`envForge`, which `storeStepL`
-- has always served.  Probe 1 below is therefore `forgeL` taking the
-- environment's forge OF A CERTIFICATE-CARRYING BLOCK — the first event of
-- the route S4 constrains — rather than a separate thread's first event.
-- The two `Σ`-typed LTS steps are at the SHIPPED composite
-- `nodeLogicL nA st₀` — threads, stores and all.
--
-- THE LEVELS DIFFER, AND THE DIFFERENCE MATTERS.  Probes 1 and 2 are LTS
-- steps of the FULL COMPOSITE `nodeLogicL nA st₀`.  Probes 3 and 4 are
-- STORE-LOCAL: they are `viewV` facts about the ISOLATED `voteStore nA _`,
-- not about the composite.  Probes 5 and 6 are about the SPECIFICATION, not
-- about any process at all.  Nothing here may be quoted as a fact about the
-- composite except probes 1 and 2.
--
-- THE RENDEZVOUS IS STILL WITHHELD (probes 3 and 4).  Taking the first event
-- does NOT buy the deposit: for a cert-carrying block `forgeL` must next take
-- the `stHasCert r` rendezvous, and `voteStore` offers it only for an RB hash
-- already in its `certs` list.  At the one hash `rCert`, from an empty `certs` the offer is
-- `nothing` (`uncertified-blocks`) and with `rCert` certified it is `just`
-- (`certified-offers`).  That is a PROCESS fact about the store, at ONE hash —
-- the ∀ version is structural (`NodeLogicL.offerCerts`) and is NOT what these
-- two pin.
--
-- THE SPEC GATE IS NON-TRIVIAL AT THE SHIPPED INSTANCE (probes 5 and 6), which
-- is a separate claim from both of the above.  `CertRbOriginBad`'s
-- `gate-uncertified`/`gate-certified` are stated at its own `leiosLP₃`; they
-- transfer to `leiosLP` only by the two `rbCert` expressions happening to be
-- byte-identical, which is an inference across instances and not a proof.
-- `gate-uncertified-at-leiosLP`/`gate-certified-at-leiosLP` below are the same
-- pair stated AT `leiosLP`, so the whole "the shipped instance's `rbCert` is
-- non-trivial" claim rests on a proof term.
--
-- It proves no property of the protocol; it is a non-vacuity certificate for
-- the environment routes.  Nothing imports it.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.NodeLogicLSanity where

import Data.Unit as U
open import Data.Unit.Polymorphic using (tt)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe′; is-just)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (Dir; lo)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; env; envForge; envSubmit; store; stPut)
open import Cardano_network.Data leiosLParams using (Payload)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.CertRbOrigin as CRO

open Params leiosLParams using (Block; RbHash; Tx; EB)
open NL.Generic leiosLParams leiosLLine apiES using (storeES)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using (nodeLogicL; st₀; hasCertEv; voteStore; bodyStep; memStep; getBodyEv; getTxEv; lacksBodyEv; lacksTxEv; serveTxs)
-- S4's specification gate AT THE SHIPPED `leiosLP` (the control states the same gate at
-- its own `leiosLP₃`; this open is what makes probes 5 and 6 facts about the ship line)
open CRO.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using (certRbGate)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (viewV; Ret)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloL; Par-soloR)

-- the node under test: node 0 of the Linear-Leios line, whose home endpoint is
-- `(link 0 , lo)` — so its `store`/`env` channels are `store/env fzero lo _`
nA : Fin 3
nA = fzero

-- the ranking block the environment offers on the forge channel.  At `leiosLP` its body
-- certifies the ranking block `just true` (`rbCert`), so it is the forge route S4 gates.
bCert : Block
bCert = just false

-- the transaction the environment submits
txA : Tx
txA = true

-- the ranking block `bCert`'s certificate names, i.e. the one `forgeL` must find
-- already certified here before it may deposit
rCert : RbHash
rCert = just true

------------------------------------------------------------------------
-- PROBE 1 — the forge takes its first event, FOR A CERTIFICATE-CARRYING BLOCK
--
-- `env … envForge` IS in `storeES`, so this is a `Par-sync`: the THREAD side is
-- `forgeL`, the leftmost of the node-level threads (`Par-soloL` past the other
-- fourteen); the STORE side is `storeStepL`'s forge arm, offered by the leftmost store
-- of the group.  The block offered is `bCert`, whose body carries a certificate, so
-- this is the first event of the very route S4 gates — there is no separate
-- certificate-forge channel to take it.
------------------------------------------------------------------------

-- the environment's forge event at node 0.  Its carrier is the `(optional EB , RB)`
-- pair, and the offer below pairs `bCert` with the EB it announces, so the
-- announcement guard `forgeOK` accepts it.
evForge : Net_Api Payload (Maybe EB × Block)
evForge = env fzero lo envForge

-- THE WITNESS: the SHIPPED composite `nodeLogicL nA st₀` — all fifteen threads
-- synchronised with all five stores — fires `env … envForge` carrying a cert-RB
forgeCert-first-step :
  Σ[ P ∈ Proc ] (nodeLogicL nA st₀
                   ─[ ev (evl (evLabel (Maybe EB × Block) evForge (just false , bCert))) ]─► P)
forgeCert-first-step =
  _ , Par-sync storeES _ _ _ {e = evForge} {a = just false , bCert} tt
        (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
        (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)

------------------------------------------------------------------------
-- PROBE 2 — the submission thread takes its first event
--
-- Same shape one level deeper: `submit` is the fourth node-level thread (three
-- `Par-soloR`s past `forgeL`, `ebIndex` and `voter`), and the store side is `memStep`'s
-- new arm in the fourth store (three `Par-soloR`s past the RB, EB-entry and body
-- stores).
------------------------------------------------------------------------

-- the environment's transaction-submission event at node 0
evSubmit : Net_Api Payload Tx
evSubmit = env fzero lo envSubmit

-- THE WITNESS: the same shipped composite fires `env … envSubmit`, so the node now has
-- an environment route into its mempool
submit-first-step :
  Σ[ P ∈ Proc ] (nodeLogicL nA st₀ ─[ ev (evl (evLabel Tx evSubmit txA)) ]─► P)
submit-first-step =
  _ , Par-sync storeES _ _ _ {e = evSubmit} {a = txA} tt
        (Par-soloR _ _ _ _ (λ ())
          (Par-soloR _ _ _ _ (λ ())
            (Par-soloR _ _ _ _ (λ ())
              (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl) refl) refl)
        (Par-soloR _ _ _ _ (λ ())
          (Par-soloR _ _ _ _ (λ ())
            (Par-soloR _ _ _ _ (λ ())
              (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl) refl) refl)

------------------------------------------------------------------------
-- PROBES 3 AND 4 — the reachable forge route is still GATED
------------------------------------------------------------------------

-- FROM EMPTY STORES THE GATE BITES: the vote store has certified nothing, so it offers
-- no `stHasCert (just true)` and `forgeL` — which has just taken the forge event —
-- can go no further.  Merging the routes kept them reachable; it did not open the gate.
uncertified-blocks :
  viewV (PTree.force (voteStore nA ([] , []))) (U.⊤ , hasCertEv nA rCert) U.tt ≡ nothing
uncertified-blocks = refl

-- … AND THE GATE IS NOT VACUOUS: once `rCert` is in the vote store's `certs` list the
-- very same rendezvous IS offered, and the deposit may proceed.  Together with
-- `uncertified-blocks` this pins that what stops the unearned deposit on the reachable
-- forge route is the MISSING CERTIFICATE and nothing else.
certified-offers :
  Σ[ P ∈ Proc ]
    (viewV (PTree.force (voteStore nA ([] , rCert ∷ []))) (U.⊤ , hasCertEv nA rCert) U.tt
     ≡ just P)
certified-offers = _ , refl

------------------------------------------------------------------------
-- PROBES 5 AND 6 — the SPECIFICATION gate is non-trivial AT `leiosLP`
--
-- These are about `CertRbSpecT`, not about any process.  They are the proof term the
-- `rbCert` decision rests on: with the old `rbCert = λ _ → nothing` the first of them
-- was FALSE (`certRbGate` was identically `true` at this instance), so between them they
-- say the shipped gate is neither constantly true nor constantly false.
------------------------------------------------------------------------

-- AT THE SHIPPED INSTANCE the gate REFUSES the deposit of `bCert` when nothing is
-- minted: `rbCert bCert` is `just rCert` and `rCert` is not in the empty minted set
gate-uncertified-at-leiosLP :
  certRbGate [] (Block , store fzero lo stPut) bCert ≡ false
gate-uncertified-at-leiosLP = refl

-- … and it LICENSES the same deposit once `rCert` has been minted AT THE ENDPOINT THE
-- DEPOSIT IS MADE AT.  So at `leiosLP` the gate is a real test, and what it tests is the
-- certificate and the endpoint and nothing else.  Node `nA` has degree 1, so the endpoint
-- it certifies at is already its own home endpoint `(fzero , lo)`.
gate-certified-at-leiosLP :
  certRbGate (((fzero , lo) , rCert) ∷ []) (Block , store fzero lo stPut) bCert ≡ true
gate-certified-at-leiosLP = refl

-- A held body offers its positive read and preserves the body-store state.
get-body-held :
  viewV (PTree.force (bodyStep nA (true ∷ []))) (EB , getBodyEv nA true) true
    ≡ just (Ret (true ∷ []))
get-body-held = refl

-- An absent body hash has no positive read, complementing its negative offer.
get-body-missing :
  viewV (PTree.force (bodyStep nA (true ∷ []))) (EB , getBodyEv nA false) false ≡ nothing
get-body-missing = refl

-- A held body has no negative read at the shipped Boolean-hash instance.
lacksIffNotHeld-body-held :
  viewV (PTree.force (bodyStep nA (true ∷ []))) (U.⊤ , lacksBodyEv nA true) U.tt ≡ nothing
lacksIffNotHeld-body-held = refl

-- A missing body offers a negative read that leaves the store unchanged.
lacksIffNotHeld-body-missing :
  viewV (PTree.force (bodyStep nA (true ∷ []))) (U.⊤ , lacksBodyEv nA false) U.tt
    ≡ just (Ret (true ∷ []))
lacksIffNotHeld-body-missing = refl

-- A held transaction offers its positive read and preserves the mempool state.
get-tx-held :
  viewV (PTree.force (memStep nA (true ∷ []))) (Tx , getTxEv nA true) true
    ≡ just (Ret (true ∷ []))
get-tx-held = refl

-- An absent transaction hash has no positive read, complementing its negative offer.
get-tx-missing :
  viewV (PTree.force (memStep nA (true ∷ []))) (Tx , getTxEv nA false) false ≡ nothing
get-tx-missing = refl

-- A held transaction has no negative read at the same instance.
lacksIffNotHeld-tx-held :
  viewV (PTree.force (memStep nA (true ∷ []))) (U.⊤ , lacksTxEv nA true) U.tt ≡ nothing
lacksIffNotHeld-tx-held = refl

-- A missing transaction offers a negative read that leaves the mempool unchanged.
lacksIffNotHeld-tx-missing :
  viewV (PTree.force (memStep nA (true ∷ []))) (U.⊤ , lacksTxEv nA false) U.tt
    ≡ just (Ret (true ∷ []))
lacksIffNotHeld-tx-missing = refl

-- A requested offset past the shipped body's table stops the serving thread.
missingOffsetStops : serveTxs nA fzero lo (false , U.tt) (100 ∷ []) [] ≡ Op.Stop
missingOffsetStops = refl

-- A valid offset can consume an unwritten-transaction read only by stopping.
unwrittenTxStops : viewV (PTree.force (serveTxs nA fzero lo (true , U.tt) (0 ∷ []) []))
  (U.⊤ , lacksTxEv nA true) U.tt ≡ just Op.Stop
unwrittenTxStops = refl

-- A missing offset never sends an accumulated partial reply.
missingOffsetDiscardsPartial : serveTxs nA fzero lo (false , U.tt) (100 ∷ []) ((0 , true) ∷ []) ≡ Op.Stop
missingOffsetDiscardsPartial = refl


import Data.List.Properties
import Cardano_network.Parametric.Leios.LeiosParams as LP
open import Data.Nat using (s≤s; z≤n)
open import Cardano_network.Net leiosLParams
  using (apiLP; lfpSendBlockRequest; lfpRecvBlock; lfpSendBlockTxsRequest; lfpRecvBlockTxs)

-- A body above the fixed wire ceiling exercises the oversized stop.
lpOver : LP.LeiosParams leiosLParams
lpOver = record leiosLP { ebTxs = λ _ → Data.List.replicate 17143 (true , U.tt) }

-- A two-entry body with singleton chunks exercises two successive requests.
lpTwo : LP.LeiosParams leiosLParams
lpTwo = record leiosLP { ebTxs = λ _ → (true , U.tt) ∷ (false , U.tt) ∷ [] }

-- Instantiate the body table above the fixed decoder ceiling.
module Over = NLL.Generic leiosLParams lpOver leiosLLine apiES (λ n → n)
-- Instantiate the two-entry table with singleton chunks.
module Two = NLL.Generic leiosLParams lpTwo leiosLLine apiES (λ n → n)
-- Keep hash/reply rejection probes at the shipped instance.
module Ship = NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)

-- Follow a concrete visible offer; absence is mapped to Stop for these computation probes.
after : ∀ {A : Set} → Proc → Net_Api Payload A → A → Proc
after P e a = maybe′ (λ Q → Q) Op.Stop (viewV (PTree.force P) (_ , e) a)

-- An EB with maxTxs + 1 entries stops immediately after its receive.
oversizedEBStops :
  viewV (PTree.force (after (Over.fetchBody nA fzero lo ((true , U.tt) , U.tt))
    (apiLP fzero lo lfpSendBlockRequest) (true , U.tt)))
    (_ , apiLP fzero lo lfpRecvBlock) true ≡ just Op.Stop
oversizedEBStops rewrite Data.List.Properties.length-replicate {A = Bool × U.⊤} 17143 {x = (true , U.tt)} = refl

-- A hash-mismatched body stops even when its table fits the ceiling.
hashMismatchStops :
  viewV (PTree.force (after (Ship.fetchBody nA fzero lo ((false , U.tt) , U.tt))
    (apiLP fzero lo lfpSendBlockRequest) (false , U.tt)))
    (_ , apiLP fzero lo lfpRecvBlock) true ≡ just Op.Stop
hashMismatchStops = refl

-- A bad second entry prevents the good first entry from being deposited.
partialReplyDepositsNothing :
  Ship.putChecked nA true ((0 , true) ∷ (0 , false) ∷ []) ≡ Op.Stop
partialReplyDepositsNothing = refl

-- Fetching the body first reaches the first singleton request, followed by its receive.
firstChunk : Proc
firstChunk = after (Two.fetchTxs nA fzero lo (true , U.tt)) (Two.getBodyEv nA true) true

-- A matching reply deposits its transaction before the second request is available.
secondChunk : Proc
secondChunk = after (after (after firstChunk (apiLP fzero lo lfpSendBlockTxsRequest)
  ((true , U.tt) , 0 ∷ [])) (apiLP fzero lo lfpRecvBlockTxs)
    ((true , U.tt) , (0 , true) ∷ [])) (Two.putTxEv nA) true

-- Both singleton requests are offered in order by the actual fetchTxs residuals.
twoChunksTwoRequests :
  (is-just (viewV (PTree.force firstChunk) (_ , apiLP fzero lo lfpSendBlockTxsRequest)
    ((true , U.tt) , 0 ∷ [])) ≡ true)
  × (is-just (viewV (PTree.force secondChunk) (_ , apiLP fzero lo lfpSendBlockTxsRequest)
    ((true , U.tt) , 1 ∷ [])) ≡ true)
twoChunksTwoRequests = refl , refl

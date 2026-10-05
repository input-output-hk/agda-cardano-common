{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE LIVENESS PROBES FOR THE TWO REPAIRED
-- THREADS of `NodeLogicL`: `forgeCert` and `submit` really do take their
-- first event INSIDE THE FULL `nodeLogicL`.
--
-- WHAT THIS ANSWERS.  As originally shipped, `storeStepL` offered `envForge`
-- and `memStep` offered no `env` channel at all, while `NodeLogic.storeSet`
-- puts EVERY `env` channel in the rendezvous set `storeES`.  A synchronised
-- event fires only when BOTH operands of `∥⇘ storeES ⇙` offer it, so
-- `forgeCert` (first event `env home(n) envForgeCert`) and `submit` (first
-- event `env home(n) envSubmit`) were BLOCKED AT THEIR FIRST EVENT: the
-- cert-RB forge route was unreachable and the mempool had no environment
-- route in.  `storeStepL` and `memStep` each gained one pure-rendezvous arm;
-- the two `Σ`-typed LTS steps below are the proof that the repair works, at
-- the SHIPPED composite `nodeLogicL nA st₀` — threads, stores and all.
--
-- THE LEVELS DIFFER, AND THE DIFFERENCE MATTERS.  Probes 1 and 2 are LTS
-- steps of the FULL COMPOSITE `nodeLogicL nA st₀`.  Probes 3 and 4 are
-- STORE-LOCAL: they are `viewV` facts about the ISOLATED `voteStore nA _`,
-- not about the composite.  Probes 5 and 6 are about the SPECIFICATION, not
-- about any process at all.  Nothing here may be quoted as a fact about the
-- composite except probes 1 and 2.
--
-- THE RENDEZVOUS IS STILL WITHHELD (probes 3 and 4).  Taking the first event
-- does NOT buy the deposit: `forgeCert`'s second event is the `stHasCert r`
-- rendezvous, and `voteStore` offers it only for an RB hash already in its
-- `certs` list.  At the one hash `rCert`, from an empty `certs` the offer is
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
-- the repair.  Nothing imports it.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Leios.NodeLogicLSanity where

import Data.Unit as U
open import Data.Unit.Polymorphic using (tt)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; ExtI)
open import CSP.Examples.Cardano_network.Base using (Dir; lo)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import CSP.Examples.Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; env; envSubmit; envForgeCert; store; stPut)
open import CSP.Examples.Cardano_network.Data leiosLParams using (Payload)
open import CSP.Examples.Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.Leios.NodeLogicL as NLL
import CSP.Examples.Cardano_network.Parametric.Leios.CertRbOrigin as CRO

open Params leiosLParams using (Block; RbHash; Tx)
open NL.Generic leiosLParams leiosLLine apiES using (storeES)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using (nodeLogicL; st₀; hasCertEv; voteStore)
-- S4's specification gate AT THE SHIPPED `leiosLP` (the control states the same gate at
-- its own `leiosLP₃`; this open is what makes probes 5 and 6 facts about the ship line)
open CRO.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using (certRbGate)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (viewV)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloL; Par-soloR)

-- the node under test: node 0 of the Linear-Leios line, whose home endpoint is
-- `(link 0 , lo)` — so its `store`/`env` channels are `store/env fzero lo _`
nA : Fin 3
nA = fzero

-- the ranking block the environment offers on the certificate-forge channel.  At
-- `leiosLP` its body certifies the ranking block `just true` (`rbCert`).
bCert : Block
bCert = just false

-- the transaction the environment submits
txA : Tx
txA = true

-- the ranking block `bCert`'s certificate names, i.e. the one `forgeCert` must find
-- already certified here before it may deposit
rCert : RbHash
rCert = just true

------------------------------------------------------------------------
-- PROBE 1 — the certificate forge takes its first event
--
-- `env … envForgeCert` IS in `storeES`, so this is a `Par-sync`: the THREAD side is
-- `forgeCert`, reached past `forgeL` (`Par-soloR`) and ahead of the other fourteen
-- threads (`Par-soloL`); the STORE side is `storeStepL`'s new arm, offered by the
-- leftmost store of the group.  Before the repair the store side did not exist and
-- this step was underivable.
------------------------------------------------------------------------

-- the environment's certificate-forge event at node 0
evForgeCert : Net_Api Payload Block
evForgeCert = env fzero lo envForgeCert

-- THE WITNESS: the SHIPPED composite `nodeLogicL nA st₀` — all sixteen threads
-- synchronised with all five stores — fires `env … envForgeCert`
forgeCert-first-step :
  Σ[ P ∈ Proc ] (nodeLogicL nA st₀ ─[ ev (evl (evLabel Block evForgeCert bCert)) ]─► P)
forgeCert-first-step =
  _ , Par-sync storeES _ _ _ {e = evForgeCert} {a = bCert} tt
        (Par-soloR _ _ _ _ (λ ())
          (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl)
        (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)

------------------------------------------------------------------------
-- PROBE 2 — the submission thread takes its first event
--
-- Same shape one level deeper: `submit` is the fifth node-level thread (four
-- `Par-soloR`s past `forgeL`, `forgeCert`, `ebIndex` and `voter`), and the store side
-- is `memStep`'s new arm in the fourth store (three `Par-soloR`s past the RB, EB-entry
-- and body stores).
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
              (Par-soloR _ _ _ _ (λ ())
                (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl) refl) refl) refl)
        (Par-soloR _ _ _ _ (λ ())
          (Par-soloR _ _ _ _ (λ ())
            (Par-soloR _ _ _ _ (λ ())
              (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl) refl) refl)

------------------------------------------------------------------------
-- PROBES 3 AND 4 — the reachable forge route is still GATED
------------------------------------------------------------------------

-- FROM EMPTY STORES THE GATE BITES: the vote store has certified nothing, so it offers
-- no `stHasCert (just true)` and `forgeCert` — which has just taken its first event —
-- can go no further.  The repair made the route reachable; it did not open it.
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

-- … and it LICENSES the same deposit once `rCert` has been minted.  So at `leiosLP` the
-- gate is a real test, and what it tests is the certificate and nothing else.
gate-certified-at-leiosLP :
  certRbGate (rCert ∷ []) (Block , store fzero lo stPut) bCert ≡ true
gate-certified-at-leiosLP = refl

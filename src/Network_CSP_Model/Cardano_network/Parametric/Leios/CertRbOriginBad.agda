{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE NEGATIVE CONTROL FOR S4: the `stHasCert`
-- RENDEZVOUS is LOAD-BEARING.
--
-- `CertRbOrigin.certRbSound` proves `CertRbSpecT ⊑T nodeP n (nodeLogicL n st₀)`
-- for every `Params`, every `LeiosParams`, every topology and every node: a
-- certificate-carrying ranking block enters the block store by the FORGE
-- ROUTE only after this node certified the RB that certificate names.
-- `NodeLogicL.forgeCert` earns its deposit with ONE rendezvous —
-- `hasCertEv n r ⟶₀ …`, on a channel `voteStore` offers only for the hashes
-- already in its `certs` list.  Delete that rendezvous — `forgeCertBad`
-- below deposits straight away — and the property FAILS, machine-checked:
-- the node forges and stores a block certifying an RB it never certified.
--
-- THE WRITE-UP RULE — READ THIS BEFORE QUOTING EITHER RESULT.
-- `certRbSound` is ∀-`Params`, ∀-`LeiosParams`, ∀-topology, ∀-node and
-- premise-free.  THE REFUTATION IS NOT: it is at the concrete `leiosLParams`
-- line, at node 0, under a NON-TRIVIAL `rbCert` this module supplies itself,
-- over a REDUCED composite (see below).  Never state the two quantifications
-- in one sentence, and never read a system-level break out of the refutation.
-- Quote it as "the `stHasCert` guard is load-bearing", never as "certificate
-- RBs are unsound".
--
-- WHY THE CONTROL SUPPLIES ITS OWN `LeiosParams`.  `leiosLP₃` is `leiosLP`
-- with the single field `rbCert` changed and nothing else, exactly as
-- `CertSoundBad` supplies its own oracle.  It was introduced when
-- `LeiosInstanceL.leiosLP` still had `rbCert = λ _ → nothing` — no block
-- carried a certificate, `certRbGate` was `true` everywhere and the control
-- would have been VACUOUS.  `leiosLP` now carries the SAME non-trivial
-- `rbCert` (the repair round closed that gap), so the update is no longer
-- load-bearing; it is kept so that this control's statement is pinned to a
-- `rbCert` of its own and does not move with the shipped instance.
--
-- ============ WHY THE COMPOSITE IS REDUCED, AND EXACTLY HOW ============
--
-- WHY THIS COMPOSITE, AND WHAT CHANGED UNDER IT.  When Task 10 wrote this
-- control, a full-`nodeLogicL` trace was not writable at all: `forgeCert`'s
-- first event `env home(n) envForgeCert` is INSIDE `storeES`
-- (`forgeCertEv-in-storeES` below, by `refl`), no store offered it, and under
-- `∥⇘ storeES ⇙` a synchronised event fires only when BOTH operands offer it
-- (`CSP.Operators.par-pVis`: `... | yes _ | _ | _ = nothing`), so the thread —
-- honest or broken — was blocked at its first event.  R1 REPAIRED THAT:
-- `storeStepL` now has an `envForgeCert` arm.  R2 RESTATED THE CONTROL, and
-- the restatement is STRICTLY STRONGER: the composite below is
-- `nodeP nA (nodeLogicL`'s own composite`)` with ONE slot changed,
-- `forgeCertBad` in place of `forgeCert`, and the bad trace now survives BOTH
-- the store rendezvous and the peer bundle.  The old caveat — that the
-- refutation reached only the load-bearing HALF (`wf-threads`) and not
-- `CertRbSpecT ⊑T nodeP …` — IS RETIRED: the statement refuted is now
-- literally `CertRbSpecT ⊑T nodeP nA (…)`, the shape `certRbSound` has.
--
-- WHY IT SURVIVES THE STORES, which was the open question.  Both events of
-- the defect are in `storeES`, so both are now rendezvous, and both partners
-- exist: `storeStepL`'s new `envForgeCert` arm serves event 1, and its
-- `putEv` arm — DELIBERATELY UNGATED, the block store accepts any block —
-- serves event 2.  Neither event collides: `forgeL` heads its loop at
-- `forgeEv`, not `putEv`, so the `par-brBoth` introduction this round built
-- for S2/S2′/S3 is NOT needed here, and every bypassed operand discharges
-- its `viewV … ≡ nothing` obligation by `refl`.
--
-- THE SUBSTITUTION IS NOT WHAT BREAKS S4, and that is machine-checked:
-- `certRbSound-node-good` at the bottom is `CertRbOrigin.certRbSound` ITSELF
-- at `leiosLP₃` and node 0 — the positive theorem, no separate assembly — so
-- the A/B differs in exactly one thread and in nothing else.
--
-- WHAT THE REFUTATION SPENDS.  Two independent halves:
--
--   * the IMPLEMENTATION half — `bad-cert-fires`: the broken node has the
--     two-event trace ⟨the environment offering the certificate block
--     `just false`, the deposit of that block⟩, FROM EMPTY STORES;
--   * the SPECIFICATION half — `noForgeCert`: that same trace is not a trace
--     of `CertRbSpecT`.  `envForgeCert` mints nothing, so when the deposit
--     fires the minted set is still empty while the block certifies the RB
--     `just true`.  `gate-uncertified` and `gate-certified` pin that the
--     refusal is the MISSING CERTIFICATE and nothing else.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.CertRbOriginBad where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (Dir; lo)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine; leiosLDecEqBlock)
open import Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; Link; store; stPut; env; envForgeCert)
open import Cardano_network.Data leiosLParams using (Payload)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.CertRbOrigin as CRO

open Params leiosLParams using (Block; RbHash; decBlock)

-- (NO `DecEq Block` INSTANCE IS DECLARED HERE.  At `leiosLParams` `Block = Maybe Bool`
-- and `Class.DecEq` itself exports `DecEq-Maybe`, so a declared instance leaves an
-- unsolved constraint with two candidates — the Task-7 ruling, measured again here as
-- `t10-certrboriginbad-01.log`.  The broken thread's `!`-output NAMES `decBlock`, which
-- is also the term instance search picks inside `NodeLogicL.Generic`, where `Block` is
-- abstract and `decBlock` is the only candidate.)

------------------------------------------------------------------------
-- THE CONTROL'S OWN `LeiosParams`
------------------------------------------------------------------------

-- `LeiosInstanceL.leiosLP` with the block `just false` marked as carrying a certificate
-- for the ranking block `just true`, and NOTHING else changed.  The shipped `leiosLP`
-- now says exactly this too, so the update is a no-op in value; it stays because this
-- control's statement must not follow a later change to the shipped instance.
leiosLP₃ : LeiosP.LeiosParams leiosLParams
leiosLP₃ = record leiosLP
  { rbCert = λ b → if ⌊ DecEq._≟_ leiosLDecEqBlock b (just false) ⌋
                   then just (just true) else nothing }

-- THE AGREEMENT, AS A PROOF TERM RATHER THAN A SENTENCE.  The comment above says the
-- override and the shipped field currently coincide; a later edit to `LeiosInstanceL`
-- would desync that silently.  This `refl` goes RED instead, which is the point of it.
-- It does not make the control depend on the shipped field — every statement below is
-- still at `leiosLP₃`.
rbCert-agrees : LeiosP.LeiosParams.rbCert leiosLP₃ ≡ LeiosP.LeiosParams.rbCert leiosLP
rbCert-agrees = refl

open NL.Generic leiosLParams leiosLLine apiES using (storeES; putEv)
open NLL.Generic leiosLParams leiosLP₃ leiosLLine apiES (λ n → n)
  using ( StateL; st₀; forgeCertEv; forgeL; forgeCert; ebIndex; voter; submit
        ; certSink; allThreadsL; nodeLogicL
        ; blockStoreL; ebStore; bodyStore; mempool; voteStore )
-- S4 at this instance, under the control's own `rbCert`: the five parameters
-- `NodeLogicL.Generic` takes, with `VoterId = Node = Fin 3` and the identity voter map
open CRO.Generic leiosLParams leiosLP₃ leiosLLine apiES (λ n → n)
  using ( Minted; CertRbSpecT; certRbGate; originOffer; OriginSpecAt
        ; soundLogic; wf-threads; nodeP; certRbSound )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( EventSet; Ret; Skip; pchoice; iter-bind; _>>=_; loop0; _⦀_; _∥⇘_⇙_
              ; Prefix; Output )

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
-- being `(link 0 , lo)` — so its store and env channels are `store/env fzero lo _`
nA : Fin 3
nA = fzero

-- THE CERTIFICATE-CARRYING BLOCK the environment offers: under `leiosLP₃` its body
-- certifies the ranking block `just true`, which this node has never certified
bCert : Block
bCert = just false

-- THE BROKEN FORGE: `NodeLogicL.forgeCert` with the `stHasCert` rendezvous DELETED.
-- Same environment channel, same dispatch on `rbCert`, same deposit — the ONLY
-- difference is that the node no longer waits for its own vote store to have certified
-- the ranking block the certificate names.
forgeCertBad : Fin 3 → Proc
forgeCertBad n =
  loop0 (forgeCertEv n ⟶ (λ b →
    maybe′ (λ _ → Output ⦃ decBlock ⦄ (putEv n) b Skip) Skip
           (LeiosP.LeiosParams.rbCert leiosLP₃ b)))

-- THE CONTROL'S LOGIC: `nodeLogicL`'s composite EXACTLY — the six node-level threads,
-- every incident endpoint's ten, and the same five stores on the same `∥⇘ storeES ⇙`
-- rendezvous — with ONE slot changed, `forgeCertBad` in place of `forgeCert`.  Nothing
-- is pruned, and unlike S2/S2′/S3 nothing had to be: see the header.
nodeLogicLCertRbBad : Fin 3 → StateL → Proc
nodeLogicLCertRbBad n (held , es , bs , ts , vs) =
  (forgeL n ⦀ (forgeCertBad n ⦀ (ebIndex n ⦀ (voter n ⦀ (submit n ⦀
     (certSink n ⦀ allThreadsL n))))))
    ∥⇘ storeES ⇙
  (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀ (mempool n ts ⦀ voteStore n vs))))

-- THE PROCESS UNDER TEST: node 0's prototype peer bundle synchronised on `apiES` with
-- the broken logic, FROM `st₀` — no seeding, exactly the state `certRbSound` is at.
badNode : Proc
badNode = nodeP nA (nodeLogicLCertRbBad nA st₀)

-- `env … envForgeCert` IS in `storeES`, so under `∥⇘ storeES ⇙` it fires only if the
-- store group offers it too.  No store did when this control was written; `storeStepL`
-- has had the arm since R1, which is what lets step 1 below be a `Par-sync`.
forgeCertEv-in-storeES : EventSet.mem storeES (Block , env fzero lo envForgeCert) bCert
forgeCertEv-in-storeES = tt

------------------------------------------------------------------------
-- The two visible events of the bad trace
------------------------------------------------------------------------

-- event 1: the environment offers the certificate-carrying ranking block.  Mints
-- NOTHING — a forge is not a certification.
evForgeCert : Event√ (⊤ {0ℓ})
evForgeCert = evl (evLabel Block (env fzero lo envForgeCert) bCert)

-- event 2: THE UNEARNED DEPOSIT — a block certifying `just true` enters the block store
-- although this node never fired `stHasCert (just true)`
evPut : Event√ (⊤ {0ℓ})
evPut = evl (evLabel Block (store fzero lo stPut) bCert)

------------------------------------------------------------------------
-- The three steps
--
-- Both events are in `storeES` and OUTSIDE `apiES`, so each is a `Par-soloR` past the
-- peer bundle wrapping a `Par-sync` of the thread group with the store group.  Neither
-- event collides, so every other thread and store is passed by `Par-soloL`/`Par-soloR`
-- with a `viewV … ≡ nothing` obligation discharged by `refl`.
------------------------------------------------------------------------

-- STEP 1.  The environment's certificate forge: the broken thread (second of the six
-- node-level threads) with the block store's `envForgeCert` arm (first of the five).
step₁ : Σ[ P₁ ∈ Proc ] (badNode ─[ ev evForgeCert ]─► P₁)
step₁ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
        (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl)
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl))
    refl

-- STEP 2.  The block store's loop-back: having served the forge it returns its state to
-- `iter`, whose `sil` guard is one τ.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ τ ]─► P₂)
step₂ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _ (sSil refl)))

-- STEP 3.  THE UNEARNED DEPOSIT, with no `stHasCert` rendezvous in between: the broken
-- thread deposits and the block store's UNGATED `putEv` arm accepts.
step₃ : Σ[ P₃ ∈ Proc ] (proj₁ step₂ ─[ ev evPut ]─► P₃)
step₃ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
        (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl)
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl))
    refl

-- THE BROKEN NODE STORES A CERTIFICATE IT NEVER EARNED
bad-cert-fires : traces badNode (evForgeCert ∷ evPut ∷ [])
bad-cert-fires =
  _ , ⟹-ev (proj₂ step₁) (⟹-τ (proj₂ step₂) (⟹-ev (proj₂ step₃) ⟹-refl))

------------------------------------------------------------------------
-- The two states `CertRbSpecT` alternates between
------------------------------------------------------------------------

-- the tree type the spec's `loop` iterates over
Tree : Set → Set₁
Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

-- `loop`'s state-threading continuation: hand the new minted set back to `iter`
κ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
κ ms = Ret (inj₁ ms)

-- the `iter` step `CertRbSpecT`'s `loop` is built from
StepT : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
StepT ms = pchoice (originOffer ms) >>= κ

-- the spec's LOOP-BACK state, reached by any visible event.  The MENU state is the
-- carrier's own `OriginSpecAt`; this one has to be re-formed because `Origin`'s copy is
-- `private`, which is also why `Tree`/`κ`/`StepT` above stay.
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

-- NON-VACUITY, PINPOINTED — the very same deposit is licensed OUTRIGHT once the RB the
-- certificate names has been certified here …
gate-certified : certRbGate (just true ∷ []) (Block , store fzero lo stPut) bCert ≡ true
gate-certified = refl

-- … and refused when it has not.  So what refuses the deposit is the MISSING
-- CERTIFICATE and nothing else — exactly the rendezvous `forgeCertBad` deleted.
gate-uncertified : certRbGate [] (Block , store fzero lo stPut) bCert ≡ false
gate-uncertified = refl

-- THE GATE.  The forge minted nothing, so when the deposit fires the minted set is still
-- empty while `rbCert bCert` is `just (just true)`: `certRbGate [] _ bCert` computes to
-- `false`, the deposit is not offered and the spec's map is definitionally `nothing`.
-- The menu has no τ either, hence three clauses.
noPut : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ evPut ∷ [] ⟩ q)
noPut (⟹-τ (sSil eq) _) = case eq of λ ()
noPut (⟹-τ (sTau refl ()) _)
noPut (⟹-ev (sVis refl ()) _)

-- THE WHOLE BAD TRACE IS REFUSED, from the empty minted set the specification starts in:
-- the environment's forge is permitted, and it mints NOTHING
noForgeCert : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ evForgeCert ∷ evPut ∷ [] ⟩ q)
noForgeCert (⟹-τ (sSil eq) _) = case eq of λ ()
noForgeCert (⟹-τ (sTau refl ()) _)
noForgeCert (⟹-ev (sVis refl refl) rest) = noPut (proj₂ (backEdge {ms = []} rest))

------------------------------------------------------------------------
-- THE NEGATIVE CONTROL
------------------------------------------------------------------------

-- the certificate-RB origin property over the BROKEN thread group: exactly
-- `CertRbOrigin.CertRbSound`'s specification and order, but with `forgeCertBad` in the
-- certificate-forge slot, over the REDUCED composite of the module header
CertRbSound-node-Bad : Set₁
CertRbSound-node-Bad = CertRbSpecT ⊑T badNode

-- THE REFUTATION: dropping the `stHasCert` rendezvous BREAKS certificate-RB origin.
-- This ONE node, on this ONE instance, under this ONE `rbCert`, running the broken
-- certificate forge over the REDUCED composite, has a trace the specification forbids,
-- so the trace refinement cannot hold — the shipped theorem is not vacuous and the
-- rendezvous is load-bearing.
--
-- LEVEL: the node logic's THREAD GROUP, not the node composite — see "WHY THE COMPOSITE
-- IS REDUCED" and "WHAT THAT COSTS, HONESTLY" in the module header.  SCOPE: this
-- instance, this node, this `rbCert`.  WRITE-UP RULE: never pair this with
-- `certRbSound`'s "∀ Params", and never quote it as "certificate RBs are unsound".
certRbSound-node-FAILS : ¬ CertRbSound-node-Bad
certRbSound-node-FAILS h = noForgeCert (proj₂ (h _ bad-cert-fires))

-- THE CONTROL'S OWN CONTROL — now the POSITIVE ITSELF.  With the composite restated at
-- `nodeP nA (nodeLogicL nA st₀)` there is nothing left to compensate: the good side of
-- the A/B is `CertRbOrigin.certRbSound` at `leiosLP₃` and node 0, no separate assembly
-- and no separate composite.  So the pair above and below differs in exactly ONE thread.
certRbSound-node-good : CertRbSpecT ⊑T nodeP nA (nodeLogicL nA st₀)
certRbSound-node-good = certRbSound nA

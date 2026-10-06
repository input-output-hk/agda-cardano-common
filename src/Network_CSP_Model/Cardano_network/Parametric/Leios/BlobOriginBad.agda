{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE NEGATIVE CONTROL FOR S2′: the VOTER'S OWN
-- ATTRIBUTION is LOAD-BEARING.
--
-- `BlobOrigin.blobSound` proves `BlobSpecT ⊑T nodeP n (nodeLogicL n st₀)`
-- for every `Params`, every `LeiosParams`, every topology and every node: a
-- vote blob attributed to ANOTHER voter is deposited only if a neighbour
-- delivered that exact blob.  `NodeLogicL.voterBody` earns its deposit the
-- other way — it casts `mkVoteBlob (voterOf n) (rbHash b)`, its OWN ballot,
-- so `atVoter` is `true` at its home endpoint and no obligation arises.
-- Change ONE token — `voterBlobBad` below casts
-- `mkVoteBlob uBad (rbHash b)` with `uBad` ANOTHER node's voter, reads
-- exactly the same two stores, and nothing else differs — and the property
-- FAILS, machine-checked.  So S2′ is not true for incidental reasons: it is
-- true because the voter signs its own name.
--
-- THE WRITE-UP RULE — READ THIS BEFORE QUOTING EITHER RESULT.  `blobSound`
-- is ∀-`Params`, ∀-`LeiosParams`, ∀-topology, ∀-node and premise-free.  THE
-- REFUTATION IS NOT: it is at the concrete `leiosLParams` line, at node 0,
-- from a SEEDED block and body store, and at NODE level — it has to be, because the trace is exhibited by
-- reducing that instance's offer maps.  Never state the two quantifications
-- in one sentence, and never read a system-level break out of the
-- refutation.  Neither result is a validity statement: the prototype's vote
-- blob carries no verdict at all.
--
-- WHICH DEFECT THIS IS, AND WHICH IT IS NOT.  S2′'s gate has two disjuncts,
-- and this control breaks the FIRST: a ballot cast under someone else's
-- name, with nothing delivered.  A control breaking the SECOND — a Notify
-- client that RELABELS a delivered blob INTO A THIRD VOTER'S NAME before
-- depositing it — would refute the same specification by the same
-- `blobGate` computation (such a blob is neither at its claimed voter's
-- endpoint nor in the minted set; relabelling into the node's OWN name
-- would NOT refute it, since the first disjunct licenses that — S2, not
-- S2′, is what covers it),
-- but its trace would have to drive the whole prototype Notify exchange
-- through the peer bundle to reach a minting event.  That is a far longer
-- trace for the same refutation content, so it is NOT built here; the
-- fabrication-by-the-voter form is the one S2′'s headline names ("the node
-- never invents a blob in someone else's name").
--
-- WHY THE FIRST STEP IS A COLLISION, AND WHAT PAYS FOR IT.  The voter reads
-- `stGetAt 0`, and so do `ebIndex`, `lnServerLoopL` and `bodyOfferLoop` —
-- all at pointer 0, all as plain prefixes.  Four threads offering ONE event
-- outside the synchronisation set means `par-pVis` neither refuses nor picks
-- a side: it fires the event into an inline internal choice, so the trace
-- costs one visible step plus one τ per collision on the path.  Until R2 the
-- repo had `par-brBoth` ELIMINATIONS but no INTRODUCTION, and this control
-- therefore ran over a REDUCED composite (the broken thread and the five
-- stores alone, the other fifteen threads dropped) with a `-good`
-- compensator for the pruning.  `TraceLawsParallel.Par-brBoth` and
-- `par-brNode-τL/R` now supply the introduction, the composite below is
-- `nodeLogicL`'s own, and NOTHING IS PRUNED — so the refutation and the
-- positive are stated over the SAME composite and may be quoted as an A/B.
--
-- WHAT THE REFUTATION SPENDS.  Two independent halves:
--
--   * the IMPLEMENTATION half — `bad-blob-fires`: the broken node has the
--     trace ⟨read the held ranking block, read the body it announces,
--     deposit a vote attributed to voter 1⟩.  The first two events are the
--     honest voter's, unchanged; only the third is the defect;
--   * the SPECIFICATION half — `noGet`: that same trace is NOT a trace of
--     `BlobSpecT`.  Neither read mints anything — only a Notify votes
--     delivery does — so when the deposit fires the minted set is still
--     empty, and the deposit is at node 0's endpoint while the blob claims
--     node 1.  `atVoter-own-holds` and `atVoter-foreign` pin that the
--     refusal is the CHANGED ATTRIBUTION and nothing else.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.BlobOriginBad where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; maybe′)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (lo)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; store; stGetAt; stGetBody; stPutVote)
open import Cardano_network.Data leiosLParams using (Payload)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.BlobOrigin as BO

open Params leiosLParams
  using (Block; EB; EBHash; VoteBlob; rbHash; announcedEB; decVoteBlob)
open LeiosP leiosLParams using (LeiosEb)
open LeiosP.LeiosParams leiosLP using (mkVoteBlob)

-- the vote-blob equality the broken voter's `!`-output needs.  At a CONCRETE
-- instantiation `open Params leiosLParams using (decVoteBlob)` does not put the field
-- in instance scope, so it is re-declared.  PRIVATE: an elaboration witness of THIS
-- module's definitions, not part of its interface — and the only `DecEq VoteBlob` here,
-- so no stdlib product instance can compete (ledger gotcha 4).
private
 instance
   DecEq-VoteBlob : DecEq VoteBlob
   DecEq-VoteBlob = decVoteBlob

open NL.Generic leiosLParams leiosLLine apiES using (storeES)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using ( StateL; getAtEv; getBodyEv; putVoteEv; nodeLogicL
        ; forgeL; ebIndex; submit; certSink; allThreadsL
        ; blockStoreL; ebStore; bodyStore; mempool; voteStore )
-- S2′ at this instance: `VoterId = Node = Fin 3`, so the voter map and its inverse are
-- both the identity and the round-trip law is `refl`
open BO.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n) (λ u → u) (λ n → refl)
  using ( Minted; BlobSpecT; originOffer; OriginSpecAt; nodeP
        ; atVoter; soundOf; wf-withStores; wf-threads )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Ret; pchoice; iter-bind; _>>=_; loop; _⦀_; _∥⇘_⇙_; Prefix; Output)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_)
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using (NoRet-Par; NoRet-⦀; NoRet-loop0)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R
        ; Par-brBoth; par-brNode-τL; par-brNode-τR)

------------------------------------------------------------------------
-- THE BREAK
------------------------------------------------------------------------

-- the node under test: node 0 of the Linear-Leios line, degree 1, its only endpoint
-- being `(link 0 , lo)` — so its store channels are `store fzero lo _`
nA : Fin 3
nA = fzero

-- THE VOTER THE BROKEN THREAD IMPERSONATES: node 1, whose home endpoint is
-- `(link 0 , hi)` and therefore NOT the endpoint the deposit happens at
uBad : Fin 3
uBad = fsuc fzero

-- THE BROKEN VOTER: `NodeLogicL.voterBody` with `uBad` where the honest thread writes
-- `voterOf n`.  That is the WHOLE diff — the same `getAtEv n k`, the same
-- `announcedEB` dispatch, the same blocking `getBodyEv n h`, the same ranking block
-- named by the blob.  Only the NAME the ballot is cast under changes.
voterBlobBadBody : Fin 3 → ℕ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ
voterBlobBadBody n k =
  getAtEv n k ⟶ (λ b →
    maybe′ (λ h → getBodyEv n h ⟶ (λ _ →
                    putVoteEv n ! mkVoteBlob uBad (rbHash b) ⟶ Ret (suc k)))
           (Ret (suc k))
           (announcedEB b))

-- the broken voting thread
voterBlobBad : Fin 3 → Proc
voterBlobBad n = loop (voterBlobBadBody n) 0

-- THE CONTROL'S LOGIC: `nodeLogicL`'s composite EXACTLY — the six node-level threads,
-- every incident endpoint's ten, and the same five stores on the same `∥⇘ storeES ⇙`
-- rendezvous — with ONE slot changed, `voterBlobBad` in place of `voter`.
-- Nothing is pruned.  (Until R2 this was a REDUCED composite: `ebIndex`, the voter,
-- `lnServerLoopL` and `bodyOfferLoop` all offer `stGetAt 0`, so the full composite's
-- first step is a `par-brBoth` COLLISION, for which the repo then had eliminations but
-- no introduction.  It now has one — `TraceLawsParallel.Par-brBoth` plus
-- `par-brNode-τL/R` — so the trace below is written over the same composite the
-- POSITIVE is stated over.)
nodeLogicLBlobBad : Fin 3 → StateL → Proc
nodeLogicLBlobBad n (held , es , bs , ts , vs) =
  (forgeL n ⦀ (ebIndex n ⦀ (voterBlobBad n ⦀ (submit n ⦀
     (certSink n ⦀ allThreadsL n)))))
    ∥⇘ storeES ⇙
  (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀ (mempool n ts ⦀ voteStore n vs))))

-- a held ranking block that DOES announce an EB (`announcedEB = λ b → b` and
-- `Block = Maybe Bool` at this instance), so the voter reaches its deposit
rbSeed : Block
rbSeed = just true

-- the EB hash that ranking block announces, and the body that hashes to it (`ebHash` is
-- the identity here)
ebH : EBHash
ebH = true

-- the seeded EB body
ebSeed : EB
ebSeed = true

-- THE SEEDED STATE: the block store holds that ranking block and the BODY store holds
-- the body it announces, every other store empty.  Seeding is only a shortcut: from
-- `st₀` the same violation takes a forge and a fetch first, and the good node satisfies
-- S2′ from EVERY initial state, because `blobSound`'s proof never looks at one.
stSeeded : StateL
stSeeded = (rbSeed ∷ []) , [] , (ebSeed ∷ []) , [] , ([] , [])

-- THE PROCESS UNDER TEST: node 0's prototype peer bundle synchronised on `apiES` with
-- the BROKEN logic, from the seeded state
badNode : Proc
badNode = nodeP nA (nodeLogicLBlobBad nA stSeeded)

------------------------------------------------------------------------
-- The three visible events of the bad trace
------------------------------------------------------------------------

-- event 1: the voter takes the seeded ranking block out of the block store.  This
-- MINTS NOTHING — under S2′ only a Notify votes delivery mints.
evGetAt : Event√ (⊤ {0ℓ})
evGetAt = evl (evLabel Block (store fzero lo (stGetAt 0)) rbSeed)

-- event 2: the voter reads the body the block announces — the honest `stGetBody`
-- synchronisation, which this defect does NOT touch, and which mints nothing either
evGetBody : Event√ (⊤ {0ℓ})
evGetBody = evl (evLabel LeiosEb (store fzero lo (stGetBody ebH)) ebSeed)

-- THE FABRICATED BALLOT: a vote naming the ranking block the node really read, but cast
-- under NODE 1's name by node 0
badBlob : VoteBlob
badBlob = mkVoteBlob uBad (rbHash rbSeed)

-- the ballot the HONEST voter would have cast at the same point: same ranking block,
-- node 0's own name
goodBlob : VoteBlob
goodBlob = mkVoteBlob nA (rbHash rbSeed)

-- event 3: THE FABRICATED DEPOSIT — a blob in another voter's name that no wire
-- delivered
evPutVote : Event√ (⊤ {0ℓ})
evPutVote = evl (evLabel VoteBlob (store fzero lo stPutVote) badBlob)

------------------------------------------------------------------------
-- The seven steps
--
-- Each is stated as "there is a state such that …", so the target of one step is
-- `proj₁` of it and the next step's source (`VoteSoundBad`'s shape).  `store ∉ apiES`
-- throughout, so the peer bundle stays put (`Par-soloR`) at every step; inside the
-- logic every event IS in `storeES`, so the thread group and the store group
-- synchronise.  Steps 2-3 resolve the `stGetAt 0` collision that the full thread group
-- makes of step 1 — `par-pVis` fires such an event into an inline internal choice.
------------------------------------------------------------------------

-- STEP 1.  The block read, AND THE COLLISION: four threads offer `stGetAt 0`.
step₁ : Σ[ P₁ ∈ Proc ] (badNode ─[ ev evGetAt ]─► P₁)
step₁ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())                          -- past forgeL
        (Par-brBoth _ _ _ _ (λ ())                   -- ebIndex COLLIDES
            (sVis refl refl)
            (Par-brBoth _ _ _ _ (λ ())                   -- the voter COLLIDES
              (sVis refl refl)
              (Par-soloR _ _ _ _ (λ ())                  -- past submit
                (Par-soloR _ _ _ _ (λ ())                -- past certSink
                  (Par-soloR _ _ _ _ (λ ())              -- past clientLoop
                    (Par-soloR _ _ _ _ (λ ())            -- past serverLoopL
                      (Par-soloR _ _ _ _ (λ ())          -- past lnClientLoopL
                        (Par-brBoth _ _ _ _ (λ ())       -- lnServerLoopL COLLIDES
                          (sVis refl refl)
                          (Par-soloL _ _ _ _ (λ ())      -- bodyOfferLoop, alone
                            (sVis refl refl) refl))
                        refl) refl) refl)
                  refl) refl))) refl)
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl))
    refl

-- STEP 2.  Resolve the OUTER collision to the RIGHT: `ebIndex` stands still.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ τ ]─► P₂)
step₂ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _ (par-brNode-τR _ _ _ _ _ _)))

-- STEP 3.  Resolve the INNER collision to the LEFT: the broken voter advances and the
-- twelve threads below it stand still.
step₃ : Σ[ P₃ ∈ Proc ] (proj₁ step₂ ─[ τ ]─► P₃)
step₃ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (par-brNode-τL _ _ _ _ _ _))))

-- STEP 4.  The block store's loop-back τ.
step₄ : Σ[ P₄ ∈ Proc ] (proj₁ step₃ ─[ τ ]─► P₄)
step₄ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _ (sSil refl)))

-- STEP 5.  The body read: the broken voter (no collision — `stGetBody` is its alone)
-- with the EB-body store (third of the five).
step₅ : Σ[ P₅ ∈ Proc ] (proj₁ step₄ ─[ ev evGetBody ]─► P₅)
step₅ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
        (Par-soloR _ _ _ _ (λ ())
          (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
          refl) refl)
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
        refl) refl))
    refl

-- STEP 6.  The EB-body store's loop-back τ.
step₆ : Σ[ P₆ ∈ Proc ] (proj₁ step₅ ─[ τ ]─► P₆)
step₆ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _ (sSil refl)))))

-- STEP 7.  THE FABRICATED DEPOSIT: the broken voter with the vote store (fifth of the
-- five), which accepts ANY blob.
step₇ : Σ[ P₇ ∈ Proc ] (proj₁ step₆ ─[ ev evPutVote ]─► P₇)
step₇ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
        (Par-soloR _ _ _ _ (λ ())
          (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
          refl) refl)
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
        refl) refl) refl))
    refl

-- THE BROKEN NODE FORGES A BALLOT IN ANOTHER VOTER'S NAME: it deposits a blob
-- attributed to node 1 that no neighbour ever delivered
bad-blob-fires : traces badNode (evGetAt ∷ evGetBody ∷ evPutVote ∷ [])
bad-blob-fires =
  _ , ⟹-ev (proj₂ step₁) (⟹-τ (proj₂ step₂) (⟹-τ (proj₂ step₃) (⟹-τ (proj₂ step₄)
        (⟹-ev (proj₂ step₅) (⟹-τ (proj₂ step₆)
          (⟹-ev (proj₂ step₇) ⟹-refl))))))

------------------------------------------------------------------------
-- The two states `BlobSpecT` alternates between
------------------------------------------------------------------------

-- the tree type the spec's `loop` iterates over
Tree : Set → Set₁
Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

-- `loop`'s state-threading continuation: hand the new minted set back to `iter`
κ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
κ ms = Ret (inj₁ ms)

-- the `iter` step `BlobSpecT`'s `loop` is built from
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

-- NON-VACUITY, PINPOINTED — the SAME deposit, at the SAME endpoint, with the HONEST
-- attribution, IS licensed outright: `atVoter` is `true`, so the gate's left disjunct
-- closes it and nothing need be delivered
atVoter-own-holds : atVoter (fzero , lo) goodBlob ≡ true
atVoter-own-holds = refl

-- … and with the fabricated attribution it is `false`, because node 1's home endpoint
-- is `(link 0 , hi)` and the deposit happens at `(link 0 , lo)`.  So what refuses the
-- deposit is the CHANGED NAME and nothing else — exactly the one token `voterBlobBad`
-- altered.
atVoter-foreign : atVoter (fzero , lo) badBlob ≡ false
atVoter-foreign = refl

-- THE GATE.  Nothing has been minted — neither read is a Notify votes delivery — and
-- `atVoter` is `false`, so `blobGate [] _ badBlob` computes to `false`, the deposit is
-- not offered and the spec's map is definitionally `nothing`.  The menu has no τ
-- either, hence three clauses.
noPut : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ evPutVote ∷ [] ⟩ q)
noPut (⟹-τ (sSil eq) _) = case eq of λ ()
noPut (⟹-τ (sTau refl ()) _)
noPut (⟹-ev (sVis refl ()) _)

-- reading a BODY mints nothing — only a Notify votes delivery does
noBody : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ evGetBody ∷ evPutVote ∷ [] ⟩ q)
noBody (⟹-τ (sSil eq) _) = case eq of λ ()
noBody (⟹-τ (sTau refl ()) _)
noBody (⟹-ev (sVis refl refl) rest) = noPut (proj₂ (backEdge {ms = []} rest))

-- THE WHOLE BAD TRACE IS REFUSED.  Reading a ranking BLOCK mints nothing either, so the
-- minted set is still empty when the fabricated ballot is deposited.
noGet : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ evGetAt ∷ evGetBody ∷ evPutVote ∷ [] ⟩ q)
noGet (⟹-τ (sSil eq) _) = case eq of λ ()
noGet (⟹-τ (sTau refl ()) _)
noGet (⟹-ev (sVis refl refl) rest) = noBody (proj₂ (backEdge {ms = []} rest))

------------------------------------------------------------------------
-- THE NEGATIVE CONTROL
------------------------------------------------------------------------

-- the NODE-LEVEL blob-origin property over the BROKEN logic: exactly
-- `BlobOrigin.BlobSound`'s specification, order and node builder, but with
-- `voterBlobBad` in place of `voter`, over `nodeLogicL`'s own composite and the
-- seeded stores
BlobSound-node-Bad : Set₁
BlobSound-node-Bad = BlobSpecT ⊑T badNode

-- THE REFUTATION: casting a ballot under another voter's name BREAKS blob origin.  This
-- ONE node, on this ONE instance, running the broken voter from the seeded stores over
-- THE SAME COMPOSITE `blobSound` IS STATED OVER, has a trace the specification forbids,
-- so the trace refinement cannot hold — the shipped theorem is not vacuous and the
-- voter's own attribution is load-bearing.
--
-- LEVEL: node, not system.  SCOPE: this instance, this node, this initial state.
-- WRITE-UP RULE: never pair this with `blobSound`'s "∀ Params" — see the module
-- header.  The composite caveat is RETIRED (R2): positive and refutation now differ in
-- exactly one thread and one initial state, and both differences are compensated.
blobSound-node-FAILS : ¬ BlobSound-node-Bad
blobSound-node-FAILS h = noGet (proj₂ (h _ bad-blob-fires))

-- THE CONTROL'S OWN CONTROL — now only about the SEED.  Since R2 the composite above
-- is `nodeLogicL`'s own, so there is no pruning left to compensate for; the one thing
-- that still differs from `blobSound`'s statement is the SEEDED stores.  This is S2′ at
-- exactly those stores — the unmodified `nodeLogicL nA stSeeded`, through
-- `BlobOrigin.soundOf` and `wf-threads`, the very lemmas `blobSound` spends.  So what
-- fails above is the changed attribution and nothing else.  (`NoRet-loop0`: `forgeL`
-- heads the thread group, so the composite
-- never ticks.)
blobSound-node-good : BlobSpecT ⊑T nodeP nA (nodeLogicL nA stSeeded)
blobSound-node-good =
  soundOf nA (nodeLogicL nA stSeeded)
    (wf-withStores (wf-threads nA))
    (NoRet-Par storeES (λ _ _ → tt) (NoRet-⦀ NoRet-loop0))

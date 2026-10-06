{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE NEGATIVE CONTROL FOR S2: the `stGetBody`
-- synchronisation is LOAD-BEARING.
--
-- `VoteSound.voteSound` proves `VoteSpecT ⊑T nodeP n (nodeLogicL n st₀)`
-- for every `Params`, every `LeiosParams`, every topology and every node:
-- a node deposits no vote blob it cannot vouch for.  For a blob the node
-- casts ITSELF that means two reads, not one — the ranking block the blob
-- names AND the body of the EB that block announces — and
-- `NodeLogicL.voterBody` earns the second by BLOCKING at `stGetBody h`
-- before it votes.  Delete that one step — `voterBad` below votes on the
-- k-th held ranking block sight unseen, and NOTHING else changes — and the
-- property FAILS, machine-checked.  So S2 is not true for incidental
-- reasons: it is true because of that synchronisation.
--
-- THE WRITE-UP RULE — READ THIS BEFORE QUOTING EITHER RESULT.  `voteSound`
-- is ∀-`Params`, ∀-`LeiosParams`, ∀-topology, ∀-node and premise-free.  THE
-- REFUTATION IS NOT: it is at the concrete `leiosLParams` line, at node 0,
-- from a SEEDED block store and at NODE level — it has to be, because the trace is exhibited by reducing
-- that instance's offer maps.  Never quote the two quantifications
-- together, and never read a system-level break out of the refutation.
--
-- WHICH LEVEL.  The refutation is at NODE LEVEL, over
-- `nodeP nA (nodeLogicLBad nA stSeeded)`, exactly as
-- `Parametric.AnnounceSafeNegative` is and for the same reason: the bad
-- trace is a run of ONE node.  A SYSTEM-LEVEL refutation is NOT established
-- here and must not be inferred from what is.
--
-- WHY THE FIRST STEP IS A COLLISION, AND WHAT PAYS FOR IT.  The broken voter reads
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
-- THE SEEDED STORE — the ONLY thing left that differs from `voteSound`'s own
-- statement, and the only thing `voteSound-node-good` now compensates.
-- `stSeeded` gives the BLOCK store one ranking block
-- that announces an EB (`announcedEB = λ b → b` at this instance), so the
-- voter reaches its deposit.  From `st₀` the same violation needs a forge
-- first; seeding is the shortest trace that exhibits the break and costs the
-- statement nothing — the good node satisfies S2 from EVERY initial state,
-- because `voteSound`'s proof never looks at one.
--
-- WHAT THE REFUTATION SPENDS.  Two independent halves:
--
--   * the IMPLEMENTATION half — `bad-vote-fires`: the broken node has the
--     trace ⟨read the held ranking block, deposit a vote naming it⟩;
--   * the SPECIFICATION half — `noGet`: that same trace is NOT a trace of
--     `VoteSpecT`.  Reading the block mints `kRb`, so the first conjunct of
--     the gate is satisfied — and the deposit is STILL refused, because the
--     `kBody` conjunct is not.  The refutation therefore bites exactly on
--     the deleted step and on nothing else.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.VoteSoundBad where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (lo)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine; leiosLDecEqBlock)
open import Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; store; stGetAt; stPutVote)
open import Cardano_network.Data leiosLParams using (Payload)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.VoteSound as VS

open Params leiosLParams using (Block; VoteBlob; rbHash; decVoteBlob)
open LeiosP.LeiosParams leiosLP using (mkVoteBlob; blobRb)
instance
  -- the vote-blob equality the `!`-output of the broken voter needs
  DecEq-VoteBlob : DecEq VoteBlob
  DecEq-VoteBlob = decVoteBlob

open NL.Generic leiosLParams leiosLLine apiES using (storeES)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using ( StateL; getAtEv; putVoteEv; nodeLogicL
        ; forgeL; ebIndex; submit; certSink; allThreadsL
        ; blockStoreL; ebStore; bodyStore; mempool; voteStore )
open VS.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using ( Minted; VoteKey; kRb; voteκ; VoteSpecT; originOffer; OriginSpecAt; nodeP
        ; soundOf; wf-withStores; wf-threads )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Ret; pchoice; iter; iter-bind; _>>=_; loop; _⦀_; _∥⇘_⇙_; Prefix; Output)

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

-- THE BROKEN VOTER: it takes the k-th oldest HELD ranking block and votes on it
-- WITHOUT reading the body the block announces.  `NodeLogicL.voterBody`'s middle step —
-- `getBodyEv n h ⟶ …`, the one that mints `kBody h` — is what is deleted, and with it
-- necessarily the `maybe′ … (announcedEB b)` dispatch that only existed to bind that
-- `h` (so `voterBad` also votes on blocks announcing no EB — immaterial here, since
-- `announcedEB rbSeed ≡ just true` at the witness).  The READ and the DEPOSITED BLOB
-- are unchanged: the same `getAtEv n k` and the same `mkVoteBlob (voterOf n) (rbHash b)`.
voterBadBody : Fin 3 → ℕ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ
voterBadBody n k =
  getAtEv n k ⟶ (λ b → putVoteEv n ! mkVoteBlob n (rbHash b) ⟶ Ret (suc k))

-- the broken voting thread
voterBad : Fin 3 → Proc
voterBad n = loop (voterBadBody n) 0

-- THE CONTROL'S LOGIC: `nodeLogicL`'s composite EXACTLY — the six node-level threads,
-- every incident endpoint's ten, and the same five stores on the same `∥⇘ storeES ⇙`
-- rendezvous — with ONE slot changed, `voterBad` in place of `voter`.  Nothing is
-- pruned.  (Until R2 this was a REDUCED composite keeping the broken voter and the
-- stores alone: `voterBad`, `ebIndex`, `lnServerLoopL` and `bodyOfferLoop` all offer
-- `stGetAt 0`, and the first step of the full composite is therefore a `par-brBoth`
-- COLLISION, for which the repo then had eliminations but no introduction.  It now has
-- one — `TraceLawsParallel.Par-brBoth` plus `par-brNode-τL/R` — so the trace below is
-- written over the same composite the POSITIVE `voteSound` is stated over.)
nodeLogicLBad : Fin 3 → StateL → Proc
nodeLogicLBad n (held , es , bs , ts , vs) =
  (forgeL n ⦀ (ebIndex n ⦀ (voterBad n ⦀ (submit n ⦀
     (certSink n ⦀ allThreadsL n)))))
    ∥⇘ storeES ⇙
  (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀ (mempool n ts ⦀ voteStore n vs))))

-- a held ranking block that DOES announce an EB (`announcedEB = λ b → b` and
-- `Block = Maybe Bool` at this instance), so the voter reaches its deposit — with no
-- body ever read, because the body store is empty
rbSeed : Block
rbSeed = just true

-- THE SEEDED STATE: the block store holds that one ranking block, every other store —
-- the BODY store above all — empty
stSeeded : StateL
stSeeded = (rbSeed ∷ []) , [] , [] , [] , ([] , [])

-- THE PROCESS UNDER TEST: node 0's prototype peer bundle synchronised on `apiES` with
-- the BROKEN logic, from the seeded state
badNode : Proc
badNode = nodeP nA (nodeLogicLBad nA stSeeded)

------------------------------------------------------------------------
-- The two visible events of the bad trace
------------------------------------------------------------------------

-- event 1: the broken voter takes the seeded ranking block out of the block store.
-- This channel MINTS `kRb rbSeed` — the first conjunct of the gate, and only that.
evGetAt : Event√ (⊤ {0ℓ})
evGetAt = evl (evLabel Block (store fzero lo (stGetAt 0)) rbSeed)

-- the blob the broken voter casts: a vote naming a ranking block whose announced EB
-- body this node has never seen
badBlob : VoteBlob
badBlob = mkVoteBlob nA (rbHash rbSeed)

-- event 2: THE UNBACKED VOTE — a deposit whose `kBody` conjunct nothing has minted
evPutVote : Event√ (⊤ {0ℓ})
evPutVote = evl (evLabel VoteBlob (store fzero lo stPutVote) badBlob)

------------------------------------------------------------------------
-- The five steps
--
-- Each is stated as "there is a state such that …", so the target of one step is
-- `proj₁` of it and the next step's source (`AnnounceBadTrace`'s shape).
------------------------------------------------------------------------

-- STEP 1.  The block read — AND THE COLLISION.  `store ∉ apiES`, so the peer bundle
-- stays put (`Par-soloR`); inside the logic the event IS in `storeES`, so the thread
-- group and the block store (first of the five) synchronise.  On the thread side FOUR
-- threads offer `stGetAt 0` — `ebIndex`, `voterBad`, `lnServerLoopL` and
-- `bodyOfferLoop` — so three of the `⦀` nodes are `par-brBoth` COLLISIONS, two of them
-- on the path to `voterBad`.  `par-pVis` does not pick a side there: it fires the event
-- into an inline internal choice, which steps 2 and 3 then resolve.
step₁ : Σ[ P₁ ∈ Proc ] (badNode ─[ ev evGetAt ]─► P₁)
step₁ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())                          -- past forgeL
        (Par-brBoth _ _ _ _ (λ ())                   -- ebIndex COLLIDES
            (sVis refl refl)
            (Par-brBoth _ _ _ _ (λ ())                   -- voterBad COLLIDES
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

-- STEP 2.  Resolve the OUTER collision to the RIGHT: the branch in which `ebIndex`
-- stands still and the rest of the thread group is the one that moved.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ τ ]─► P₂)
step₂ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _ (par-brNode-τR _ _ _ _ _ _)))

-- STEP 3.  Resolve the INNER collision to the LEFT: the branch in which `voterBad`
-- advances and the twelve threads below it stand still.  After this the composite is
-- the full node logic again, with the broken voter one step on.
step₃ : Σ[ P₃ ∈ Proc ] (proj₁ step₂ ─[ τ ]─► P₃)
step₃ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (par-brNode-τL _ _ _ _ _ _))))

-- STEP 4.  The block store's loop-back: having served the block it returns its state
-- to `iter`, whose `sil` guard is one τ.
step₄ : Σ[ P₄ ∈ Proc ] (proj₁ step₃ ─[ τ ]─► P₄)
step₄ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _ (sSil refl)))

-- STEP 5.  THE UNBACKED VOTE.  Again a `storeES` rendezvous outside `apiES`, and this
-- time NO collision — `stPutVote` is offered by the broken voter alone — so the other
-- fifteen threads are passed by `Par-soloR`/`Par-soloL` and the vote store (fifth of
-- the five) accepts ANY blob.
step₅ : Σ[ P₅ ∈ Proc ] (proj₁ step₄ ─[ ev evPutVote ]─► P₅)
step₅ = _ ,
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

-- THE BROKEN NODE CASTS AN UNBACKED VOTE: it endorses a ranking block whose announced
-- endorser-block body it has never read
bad-vote-fires : traces badNode (evGetAt ∷ evPutVote ∷ [])
bad-vote-fires =
  _ , ⟹-ev (proj₂ step₁) (⟹-τ (proj₂ step₂) (⟹-τ (proj₂ step₃)
        (⟹-τ (proj₂ step₄) (⟹-ev (proj₂ step₅) ⟹-refl))))

------------------------------------------------------------------------
-- The two states `VoteSpecT` alternates between
------------------------------------------------------------------------

-- the tree type the spec's `loop` iterates over
Tree : Set → Set₁
Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

-- `loop`'s state-threading continuation: hand the new minted set back to `iter`
κ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
κ ms = Ret (inj₁ ms)

-- the `iter` step `VoteSpecT`'s `loop` is built from
StepT : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
StepT ms = pchoice (originOffer ms) >>= κ

-- the spec's LOOP-BACK state, reached by any visible event.  The MENU state is the
-- carrier's own `OriginSpecAt` (`OriginSpecAt [] ≡ VoteSpecT` is `specAt-init`, and it
-- is a computation, so the refutation below needs no transport); this one has to be
-- re-formed because `Origin`'s copy is `private`, which is also why `Tree`/`κ`/`StepT`
-- above stay.
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

-- THE MINTED SET AFTER THE BLOCK READ: the ranking block, and NOTHING about its body.
-- Since the re-keying, a mint carries the endpoint the deposit it licenses is made at,
-- and node `nA` has degree 1, so the endpoint it reads at is already its own home
-- endpoint `(fzero , lo)`.
msAfter : Minted
msAfter = ((fzero , lo) , kRb rbSeed) ∷ []

-- NON-VACUITY, PINPOINTED — the gate's RB conjunct IS satisfied.  The blob names
-- exactly the ranking block that was read, so the deposit is not refused for some
-- incidental mismatch of hashes.
rb-conjunct-holds : ⌊ DecEq._≟_ leiosLDecEqBlock (rbHash rbSeed) (blobRb badBlob) ⌋ ≡ true
rb-conjunct-holds = refl

-- … and the `voteκ` witness is nevertheless `false`, so what refuses the deposit is
-- the MISSING BODY READ and nothing else — exactly the step `voterBad` deleted
body-conjunct-fails :
  voteκ msAfter (fzero , lo) badBlob ((fzero , lo) , kRb rbSeed) ≡ false
body-conjunct-fails = refl

-- THE GATE.  With only `kRb rbSeed` minted, the deposit of `badBlob` is not offered:
-- `kRelay badBlob` is not in the list, and `ownVote` finds its `kRb` witness — the
-- hashes DO match — only to fail on the `kBody` conjunct, because `kBody true` was
-- never minted.  So `voteGate msAfter _ badBlob` computes to `false` and the offer map
-- is definitionally `nothing`.  The menu has no τ either, hence three clauses.
noPut : ∀ {q} → ¬ (OriginSpecAt msAfter ⟹⟨ evPutVote ∷ [] ⟩ q)
noPut (⟹-τ (sSil eq) _) = case eq of λ ()
noPut (⟹-τ (sTau refl ()) _)
noPut (⟹-ev (sVis refl ()) _)

-- THE WHOLE BAD TRACE IS REFUSED.  Reading the ranking block mints `kRb` and nothing
-- else, so one event later the body conjunct is still unminted and the deposit is
-- still refused.
noGet : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ evGetAt ∷ evPutVote ∷ [] ⟩ q)
noGet (⟹-τ (sSil eq) _) = case eq of λ ()
noGet (⟹-τ (sTau refl ()) _)
noGet (⟹-ev (sVis refl refl) rest) = noPut (proj₂ (backEdge {ms = msAfter} rest))

------------------------------------------------------------------------
-- THE NEGATIVE CONTROL
------------------------------------------------------------------------

-- the NODE-LEVEL vote-soundness property over the BROKEN logic: exactly
-- `VoteSound.VoteSound`'s specification and node builder, but with `voterBad` in place
-- of `voter` and the seeded block store
VoteSound-node-Bad : Set₁
VoteSound-node-Bad = VoteSpecT ⊑T badNode

-- THE REFUTATION: deleting `voterBody`'s `stGetBody` step BREAKS vote soundness.  This
-- ONE node, on this ONE instance, running the broken logic from the seeded store, has
-- a trace the specification forbids, so the trace refinement cannot hold — the shipped
-- theorem is not vacuous and the body read is load-bearing.
--
-- LEVEL: node, not system.  SCOPE: this instance, this node, this initial state — see
-- the write-up rule in the module header before pairing this with `voteSound`.  The
-- composite caveat is RETIRED (R2): the refutation is over the SAME composite
-- `voteSound` is stated over, differing in exactly one thread and one initial state.
voteSound-node-FAILS : ¬ VoteSound-node-Bad
voteSound-node-FAILS h = noGet (proj₂ (h _ bad-vote-fires))

-- THE CONTROL'S OWN CONTROL — now only about the SEED.  Since R2 the composite above
-- is `nodeLogicL`'s own, so there is no pruning left to compensate for; the one thing
-- that still differs from `voteSound`'s statement is the SEEDED store.  This is S2 at
-- exactly that state — the unmodified `nodeLogicL nA stSeeded`, through
-- `VoteSound.soundOf` and `VoteSound.wf-threads`, the very assembly `voteSound` spends.
-- So what fails above is the deleted `getBodyEv` step and nothing else.
voteSound-node-good : VoteSpecT ⊑T nodeP nA (nodeLogicL nA stSeeded)
voteSound-node-good =
  soundOf nA (nodeLogicL nA stSeeded)
    (wf-withStores (wf-threads nA))
    (NoRet-Par storeES (λ _ _ → tt) (NoRet-⦀ NoRet-loop0))

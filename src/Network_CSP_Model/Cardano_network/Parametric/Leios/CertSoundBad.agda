{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE NEGATIVE CONTROL FOR S3: the vote store's
-- ORACLE GUARD is LOAD-BEARING.
--
-- `CertSound.Sound.certSound` proves `CertSpecT ⊑T nodeP n (nodeLogicL n st₀)`
-- for every `Params`, every `LeiosParams` whose oracle is monotone, every
-- topology and every node: the node issues no certificate the oracle does
-- not grant on the blobs deposited at it.  `NodeLogicL.certify` earns that
-- by firing `stCert ! r` only under the Boolean guard
-- `certifies bs r ∧ not (memberOf r cs)`.  Delete that guard — `certifyBad`
-- below drops it WHOLE, so `voteStoreBad` certifies unconditionally on the
-- FIRST deposit, and NOTHING else changes — and the property FAILS,
-- machine-checked.  (Dropping the whole guard rather than the oracle
-- conjunct alone costs the isolation nothing: at the exhibited trace the
-- issued-certificate list is `cs = []`, so the second conjunct
-- `not (memberOf r [])` is `true` anyway and the ONLY conjunct that could
-- have refused the certificate is the oracle's.)
--
-- THE WRITE-UP RULE — READ THIS BEFORE QUOTING EITHER RESULT.  `certSound`
-- is ∀-`Params`, ∀-`LeiosParams`-with-`CertifiesMono`, ∀-topology, ∀-node.
-- THE REFUTATION IS NOT: it is at ONE concrete parameter line, at node 0,
-- from a SEEDED block and body store, and at NODE level — it has to be, because the trace is exhibited by
-- reducing that instance's offer maps.  Never state the two quantifications
-- in one sentence, and never read a system-level break out of the
-- refutation.  Neither result is a validity statement: the prototype's vote
-- blob carries no verdict at all.
--
-- WHICH LEVEL — READ THIS BEFORE QUOTING THE RESULT.  The refutation is at
-- NODE LEVEL, over `nodeP nA (nodeLogicLCertBad nA stSeeded)`, exactly as
-- `Parametric.AnnounceSafeNegative` and `Leios.VoteSoundBad` are and for
-- the same reason: the bad trace is a run of ONE node.  A SYSTEM-LEVEL
-- refutation is NOT established here and must not be inferred from what
-- is.
--
-- WHY THE FIRST STEP IS A COLLISION, AND WHAT PAYS FOR IT.  The honest voter reads
-- `stGetAt 0`, and so do `ebIndex`, `lnServerLoopL` and `bodyOfferLoop` —
-- all at pointer 0, all as plain prefixes.  Four threads offering ONE event
-- outside the synchronisation set means `par-pVis` neither refuses nor picks
-- a side: it fires the event into an inline internal choice, so the trace
-- costs one visible step plus one τ per collision on the path.  Until R2 the
-- repo had `par-brBoth` ELIMINATIONS but no INTRODUCTION, and this control
-- therefore ran over a REDUCED composite (`voter ⦀ certSink` and the five
-- stores alone, the other fourteen threads dropped) with a `-good`
-- compensator for the pruning.  `TraceLawsParallel.Par-brBoth` and
-- `par-brNode-τL/R` now supply the introduction, the composite below is
-- `nodeLogicL`'s own, and NOTHING IS PRUNED — so the refutation and the
-- positive are stated over the SAME composite and may be quoted as an A/B.
--
-- WHY THE ORACLE HAD TO BE STRENGTHENED.  `LeiosInstanceL.leiosLP` ships
-- the WEAKEST non-trivial oracle — "some blob names that RB" — and under
-- it a store that certifies on the first deposit is still SOUND: the
-- deposit that triggers the certificate is itself a blob for that RB, so
-- the gate is open and no trace is refused.  The defect is invisible at
-- that instance.  `certifies₂` below is therefore a STRICTER oracle, a
-- TWO-VOTER QUORUM: voters 0 and 1 must both have deposited a vote naming
-- the RB.  It is `⊆`-monotone (two memberships), so `CertifiesMono` holds —
-- `certMono₂` proves it — and the SAME specification `certSound` proves of
-- the good node is the one the broken node violates.  A plain "two blobs"
-- COUNTING quorum would NOT do: `_⊆_` is set inclusion, so a
-- duplicate-carrying list is a subset of a shorter one and counting is not
-- `⊆`-monotone (campaign ledger, gotcha 9).
--
-- WHAT THE REFUTATION SPENDS.  Two independent halves:
--
--   * the IMPLEMENTATION half — `bad-cert-fires`: the broken node has the
--     trace ⟨read the held ranking block, read the body it announces,
--     deposit the vote, CERTIFY⟩.  The first three events are the honest
--     voter's, unchanged; only the fourth is the defect;
--   * the SPECIFICATION half — `noGet`: that same trace is NOT a trace of
--     `CertSpecT`, because ONE blob never satisfies a two-voter quorum, so
--     the certificate's gate is shut when it fires.  `voter0-conjunct-holds`
--     and `quorum-fails` pin that the refusal is the MISSING SECOND VOTER
--     and not an incidental hash mismatch.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.CertSoundBad where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just)
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
  using (leiosLParams; leiosLP; leiosLLine; LVoteBlob)
open import Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; store; stGetAt; stGetBody; stPutVote; stCert)
open import Cardano_network.Data leiosLParams using (Payload)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc)
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.OriginSafe as OS
import Cardano_network.Parametric.Leios.CertSound as CS
-- the shared Boolean lemmas the quorum's monotonicity spends (Task 6 put them at
-- `VoteSound`'s top level; `CertSound` no longer carries copies)
open import Cardano_network.Parametric.Leios.VoteSound
  using (∧-split; ∧-join)

open Params leiosLParams using (Block; EB; EBHash; RbHash; VoteBlob; decVoteBlob; decRbHash)
open LeiosP leiosLParams using (LeiosEb)
open OS using (memberOf; memberOf-mono)

-- the vote-blob equality the broken store's menu and dedup insert need.  At a CONCRETE
-- instantiation `open Params leiosLParams using (decVoteBlob)` does not make the field
-- visible to instance search, so it is re-declared here.  PRIVATE: an elaboration
-- witness of THIS module's definitions, not part of its interface.  There is NO
-- companion `DecEq RbHash` instance: at this line `RbHash = Maybe Bool`, so a declared
-- one would compete with the stdlib's `DecEq-Maybe` (measured — an unsolved instance
-- constraint); the certificate output NAMES `decRbHash`, which is also the term
-- `NodeLogicL.certify` used (ledger gotcha 4).
private
 instance
   DecEq-VoteBlob : DecEq VoteBlob
   DecEq-VoteBlob = decVoteBlob

------------------------------------------------------------------------
-- THE STRICTER ORACLE
------------------------------------------------------------------------

-- A TWO-VOTER QUORUM: voters 0 and 1 must BOTH have cast a vote naming the ranking
-- block.  One blob never certifies, which is exactly the defect under test; and because
-- both conjuncts are memberships the oracle is `⊆`-monotone, so `CertifiesMono` holds.
-- A COUNTING quorum would NOT be admissible — see `CertSound`'s header.
certifies₂ : List LVoteBlob → Maybe Bool → Bool
certifies₂ vs r = memberOf (fzero , r) vs ∧ memberOf (fsuc fzero , r) vs

-- the Leios parameters of the control: `LeiosInstanceL.leiosLP` with the two-voter
-- quorum in place of the shipped "one blob for that RB" oracle, and nothing else
-- changed (`Params` itself is `leiosLParams`, untouched)
leiosLP₂ : LeiosP.LeiosParams leiosLParams
leiosLP₂ = record leiosLP { certifies = certifies₂ }

open LeiosP.LeiosParams leiosLP₂ using (mkVoteBlob; blobRb)
open CS.Generic leiosLParams leiosLP₂ leiosLLine apiES (λ n → n)
  using (CertifiesMono; Minted)

-- THE PREMISE, DISCHARGED at the control's oracle: a quorum, once reached, is never
-- lost when more blobs arrive
certMono₂ : CertifiesMono
certMono₂ sub r eq =
  ∧-join (memberOf-mono sub (proj₁ (∧-split eq)))
         (memberOf-mono sub (proj₂ (∧-split eq)))

open CS.Generic.Sound leiosLParams leiosLP₂ leiosLLine apiES (λ n → n) certMono₂
  using (CertSpecT; originOffer; OriginSpecAt; nodeP; soundOf; wf-withThreads; wf-stores)

open NL.Generic leiosLParams leiosLLine apiES using (storeES)
open NLL.Generic leiosLParams leiosLP₂ leiosLLine apiES (λ n → n)
  using ( StateL; Blobs; Certs; Votes; DecEq-Votes
        ; getAtEv; getBodyEv; putVoteEv; getVoteAtEv; certEv
        ; insertU; offerIx; offerCerts
        ; nodeLogicL; forgeL; forgeCert; ebIndex; voter; submit; certSink; allThreadsL
        ; blockStoreL; ebStore; bodyStore; mempool; voteStore )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Ret; pchoice; iter-bind; _>>=_; loop; _⦀_; _∥⇘_⇙_; _□_; Prefix; Output)

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

-- THE BROKEN CERTIFICATION STEP: it fires the certificate for every deposit, WITHOUT
-- consulting the oracle.  `NodeLogicL.certify`'s guard — `certifies bs r ∧ not
-- (memberOf r cs)` — is the only thing deleted.
certifyBad : Fin 3 → Blobs → Certs → RbHash
           → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Votes
certifyBad n bs cs r = Output ⦃ decRbHash ⦄ (certEv n) r (Ret (bs , r ∷ cs))

-- one step of the broken vote store: `NodeLogicL.voteStep` with `certifyBad` for
-- `certify`, byte for byte otherwise — the same deposit, the same read-pointer menu
-- and the same certificate menu
voteStepBad : Fin 3 → Votes → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Votes
voteStepBad n (bs , cs) =
    (putVoteEv n ⟶ (λ v → certifyBad n (insertU v bs) cs (blobRb v)))
  □ ((offerIx (getVoteAtEv n) bs 0 (bs , cs))
  □   offerCerts n (bs , cs) cs)

-- the broken vote store
voteStoreBad : Fin 3 → Votes → Proc
voteStoreBad n vs = loop (voteStepBad n) vs

-- THE CONTROL'S LOGIC: `nodeLogicL`'s composite EXACTLY — the six node-level threads,
-- every incident endpoint's ten, and the same `∥⇘ storeES ⇙` rendezvous — with ONE
-- slot changed, `voteStoreBad` in place of `voteStore` as the FIFTH STORE.  Nothing is
-- pruned.  (Until R2 this kept `voter ⦀ certSink` alone against the five stores:
-- `ebIndex`, `voter`, `lnServerLoopL` and `bodyOfferLoop` all offer `stGetAt 0`, so the
-- full composite's first step is a `par-brBoth` COLLISION, for which the repo then had
-- eliminations but no introduction.  It now has one — `TraceLawsParallel.Par-brBoth`
-- plus `par-brNode-τL/R` — so the trace below is written over the same composite the
-- POSITIVE `certSoundL` is stated over.)
nodeLogicLCertBad : Fin 3 → StateL → Proc
nodeLogicLCertBad n (held , es , bs , ts , vs) =
  (forgeL n ⦀ (forgeCert n ⦀ (ebIndex n ⦀ (voter n ⦀ (submit n ⦀
     (certSink n ⦀ allThreadsL n))))))
    ∥⇘ storeES ⇙
  (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀ (mempool n ts ⦀ voteStoreBad n vs))))

-- a held ranking block that DOES announce an EB (`announcedEB = λ b → b` and
-- `Block = Maybe Bool` at this instance), so the honest voter reaches its deposit
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
-- S3 from EVERY initial state.
stSeeded : StateL
stSeeded = (rbSeed ∷ []) , [] , (ebSeed ∷ []) , [] , ([] , [])

-- THE PROCESS UNDER TEST: node 0's prototype peer bundle synchronised on `apiES` with
-- the BROKEN logic, from the seeded state
badNode : Proc
badNode = nodeP nA (nodeLogicLCertBad nA stSeeded)

------------------------------------------------------------------------
-- The four visible events of the bad trace
------------------------------------------------------------------------

-- event 1: the honest voter takes the seeded ranking block out of the block store
evGetAt : Event√ (⊤ {0ℓ})
evGetAt = evl (evLabel Block (store fzero lo (stGetAt 0)) rbSeed)

-- event 2: the voter reads the body the block announces — the honest `stGetBody`
-- synchronisation, which the S3 defect does NOT touch
evGetBody : Event√ (⊤ {0ℓ})
evGetBody = evl (evLabel LeiosEb (store fzero lo (stGetBody ebH)) ebSeed)

-- the blob the honest voter casts: voter 0, naming the ranking block it read
theBlob : VoteBlob
theBlob = mkVoteBlob nA rbSeed

-- event 3: the deposit.  ONE blob — a two-voter quorum is not reached.
evPutVote : Event√ (⊤ {0ℓ})
evPutVote = evl (evLabel VoteBlob (store fzero lo stPutVote) theBlob)

-- event 4: THE UNGRANTED CERTIFICATE — the broken store certifies the ranking block on
-- the first deposit, though the oracle refuses a one-vote quorum
evCert : Event√ (⊤ {0ℓ})
evCert = evl (evLabel RbHash (store fzero lo stCert) rbSeed)

---------------------------------------------------------------------------------------------------
-- The nine steps
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
        (Par-soloR _ _ _ _ (λ ())                        -- past forgeCert
          (Par-brBoth _ _ _ _ (λ ())                     -- ebIndex COLLIDES
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
                  refl) refl))) refl) refl)
      (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl))
    refl

-- STEP 2.  Resolve the OUTER collision to the RIGHT: `ebIndex` stands still.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ τ ]─► P₂)
step₂ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (par-brNode-τR _ _ _ _ _ _))))

-- STEP 3.  Resolve the INNER collision to the LEFT: the honest voter advances and the
-- twelve threads below it stand still.
step₃ : Σ[ P₃ ∈ Proc ] (proj₁ step₂ ─[ τ ]─► P₃)
step₃ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (par-brNode-τL _ _ _ _ _ _)))))

-- STEP 4.  The block store's loop-back τ.
step₄ : Σ[ P₄ ∈ Proc ] (proj₁ step₃ ─[ τ ]─► P₄)
step₄ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _ (sSil refl)))

-- STEP 5.  The body read: the voter with the EB-body store (third of the five).
step₅ : Σ[ P₅ ∈ Proc ] (proj₁ step₄ ─[ ev evGetBody ]─► P₅)
step₅ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
        (Par-soloR _ _ _ _ (λ ())
          (Par-soloR _ _ _ _ (λ ())
            (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
            refl) refl) refl)
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

-- STEP 7.  The deposit: the voter with the BROKEN vote store (fifth of the five).
step₇ : Σ[ P₇ ∈ Proc ] (proj₁ step₆ ─[ ev evPutVote ]─► P₇)
step₇ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
        (Par-soloR _ _ _ _ (λ ())
          (Par-soloR _ _ _ _ (λ ())
            (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
            refl) refl) refl)
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
        refl) refl) refl))
    refl

-- STEP 8.  The voter's loop-back τ.
step₈ : Σ[ P₈ ∈ Proc ] (proj₁ step₇ ─[ τ ]─► P₈)
step₈ = _ ,
  Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (Par-τ-L _ _ _ _ (sSil refl))))))

-- STEP 9.  THE UNGRANTED CERTIFICATE: the broken vote store fires `stCert ! rbSeed` and
-- the certificate sink (sixth of the node-level threads) absorbs it.
step₉ : Σ[ P₉ ∈ Proc ] (proj₁ step₈ ─[ ev evCert ]─► P₉)
step₉ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
        (Par-soloR _ _ _ _ (λ ())
          (Par-soloR _ _ _ _ (λ ())
            (Par-soloR _ _ _ _ (λ ())
              (Par-soloR _ _ _ _ (λ ())
                (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
                refl) refl) refl) refl) refl)
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
        refl) refl) refl))
    refl

-- THE BROKEN NODE CERTIFIES WITHOUT A QUORUM: one honest vote, and the certificate
-- fires
bad-cert-fires : traces badNode (evGetAt ∷ evGetBody ∷ evPutVote ∷ evCert ∷ [])
bad-cert-fires =
  _ , ⟹-ev (proj₂ step₁) (⟹-τ (proj₂ step₂) (⟹-τ (proj₂ step₃) (⟹-τ (proj₂ step₄)
        (⟹-ev (proj₂ step₅) (⟹-τ (proj₂ step₆)
          (⟹-ev (proj₂ step₇) (⟹-τ (proj₂ step₈)
            (⟹-ev (proj₂ step₉) ⟹-refl))))))))

------------------------------------------------------------------------
-- The two states `CertSpecT` alternates between
------------------------------------------------------------------------

-- the tree type the spec's `loop` iterates over
Tree : Set → Set₁
Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

-- `loop`'s state-threading continuation: hand the new minted set back to `iter`
κ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
κ ms = Ret (inj₁ ms)

-- the `iter` step `CertSpecT`'s `loop` is built from
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

-- NON-VACUITY, PINPOINTED — voter 0's conjunct of the quorum IS satisfied at the
-- witness, so the certificate is not refused for some incidental mismatch
voter0-conjunct-holds : memberOf (nA , rbSeed) (theBlob ∷ []) ≡ true
voter0-conjunct-holds = refl

-- … and the quorum is nevertheless refused, so what shuts the gate is the MISSING
-- SECOND VOTER and nothing else — exactly what the deleted oracle guard tested
quorum-fails : certifies₂ (theBlob ∷ []) rbSeed ≡ false
quorum-fails = refl

-- THE GATE.  With only the one blob minted, the two-voter quorum is not reached:
-- `certifies₂ (theBlob ∷ []) rbSeed` computes to `false`, so the certificate is not
-- offered and the spec's map is definitionally `nothing`.  The menu has no τ either.
noCert : ∀ {q} → ¬ (OriginSpecAt (theBlob ∷ []) ⟹⟨ evCert ∷ [] ⟩ q)
noCert (⟹-τ (sSil eq) _) = case eq of λ ()
noCert (⟹-τ (sTau refl ()) _)
noCert (⟹-ev (sVis refl ()) _)

-- the deposit itself is permitted — it needs nothing certified — and it mints exactly
-- the one blob, so the certificate one event later is still refused
noPut : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ evPutVote ∷ evCert ∷ [] ⟩ q)
noPut (⟹-τ (sSil eq) _) = case eq of λ ()
noPut (⟹-τ (sTau refl ()) _)
noPut (⟹-ev (sVis refl refl) rest) = noCert (proj₂ (backEdge {ms = theBlob ∷ []} rest))

-- reading a BODY mints nothing — only a deposit does
noBody : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ evGetBody ∷ evPutVote ∷ evCert ∷ [] ⟩ q)
noBody (⟹-τ (sSil eq) _) = case eq of λ ()
noBody (⟹-τ (sTau refl ()) _)
noBody (⟹-ev (sVis refl refl) rest) = noPut (proj₂ (backEdge {ms = []} rest))

-- THE WHOLE BAD TRACE IS REFUSED.  Reading a ranking BLOCK mints nothing either, so the
-- minted set is still the single blob when the certificate fires.
noGet : ∀ {q} → ¬ (OriginSpecAt [] ⟹⟨ evGetAt ∷ evGetBody ∷ evPutVote ∷ evCert ∷ [] ⟩ q)
noGet (⟹-τ (sSil eq) _) = case eq of λ ()
noGet (⟹-τ (sTau refl ()) _)
noGet (⟹-ev (sVis refl refl) rest) = noBody (proj₂ (backEdge {ms = []} rest))

------------------------------------------------------------------------
-- THE NEGATIVE CONTROL
------------------------------------------------------------------------

-- the NODE-LEVEL cert-soundness property over the BROKEN logic: exactly
-- `CertSound.Sound.CertSound`'s specification, order and node builder, but with
-- `voteStoreBad` in place of `voteStore`, over `nodeLogicL`'s own composite and the
-- seeded stores
CertSound-node-Bad : Set₁
CertSound-node-Bad = CertSpecT ⊑T badNode

-- THE REFUTATION: firing `stCert` on every deposit BREAKS cert soundness against a
-- two-voter quorum.  This ONE node, on this ONE instance, running the broken store from
-- the seeded state over THE SAME COMPOSITE `certSoundL` IS STATED OVER, has a trace the
-- specification forbids, so the trace refinement cannot hold — the shipped theorem is
-- not vacuous and the oracle consultation is load-bearing.
--
-- LEVEL: node, not system.  SCOPE: this instance, this node, this initial state.  The
-- composite caveat is RETIRED (R2): positive and refutation now differ in exactly one
-- STORE and one initial state.  WRITE-UP RULE: quote this as "unsound against a two-voter
-- quorum", never as "unsound", and never in the same breath as `certSound`'s
-- "∀ Params" — see the module header.
certSound-node-FAILS : ¬ CertSound-node-Bad
certSound-node-FAILS h = noGet (proj₂ (h _ bad-cert-fires))

-- THE CONTROL'S OWN CONTROL — now only about the SEED.  Since R2 the composite above
-- is `nodeLogicL`'s own, so there is no pruning left to compensate for; the one thing
-- that still differs from `certSoundL`'s statement is the SEEDED stores.  This is S3 at
-- exactly those stores — the unmodified `nodeLogicL nA stSeeded`, through
-- `CertSound.Sound.soundOf`/`wf-withThreads`/`wf-stores`, the very lemmas `certSound`
-- spends.  So what fails above is the deleted oracle guard and nothing else.
-- (`NoRet-loop0`: `forgeL` heads the thread group, so the composite never ticks.)
certSound-node-good : CertSpecT ⊑T nodeP nA (nodeLogicL nA stSeeded)
certSound-node-good =
  soundOf nA (nodeLogicL nA stSeeded)
    (wf-withThreads (wf-stores nA (rbSeed ∷ []) [] (ebSeed ∷ []) [] []))
    (NoRet-Par storeES (λ _ _ → tt) (NoRet-⦀ NoRet-loop0))

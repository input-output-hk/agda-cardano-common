{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S3, CERT SOUNDNESS on the PROTOTYPE vote
-- model: the origin discipline, the specification it induces, and the
-- theorem at the node.
--
-- WHAT S3 SAYS.  The node never issues a certificate the certification
-- oracle does not grant on the vote blobs it has been handed.  Firing
-- `store home(n) stCert ! r` requires `certifies ms r ≡ true`, where `r` is
-- a RANKING-BLOCK hash (`RbHash` — a vote names the RB it endorses, spec
-- §4.1) and `ms` is the list of blobs DEPOSITED at that node so far: every
-- `store home(n) stPutVote ! v` mints `v`.
--
-- WHAT S3 DOES *NOT* SAY.  It is NOT a validity statement, and on the
-- prototype model it could not be one: the vote blob carries NO VERDICT at
-- all (spec §1.2 decision 4 — `blobValid` and `valid` are gone), so there is
-- no validity for `certifies` to ignore or to respect.  The theorem is
-- "certified ⇒ blobs were deposited at this node and the oracle judged them
-- enough", never "certified ⇒ the RB, or the EB it announces, is valid".
-- That a blob really came from the voter it names is S2′ and is not proved
-- anywhere; what work the depositing node did behind its OWN blob is S2
-- (`VoteSound.agda`).
--
-- THE PREMISE — A MONOTONE ORACLE.  `certGate-mono`, which the generic
-- carrier `OriginSafe.Generic.Origin` demands of every gate, is NOT
-- provable for an arbitrary `certifies`: an oracle that WITHDRAWS a
-- certificate once a disqualifying blob arrives is a legal `LeiosParams`.
-- `CertifiesMono` below is therefore an explicit hypothesis — it is
-- `LeiosParams.CertifiesMono lp` by definition — carried in the telescope of
-- the inner module `Sound`, because the SPECIFICATION itself is a module
-- application that consumes the monotonicity law.  **S3 CARRIES A PREMISE
-- AND S2 DOES NOT**: `VoteSound.voteSound` is premise-free, and no write-up
-- may present the two as equally unconditional.  At the SHIPPED oracle the
-- premise is discharged (`certMonoL` at the bottom of this file), so
-- `certSoundL` is unconditional for the nodes of `LeiosInstanceL`.
--
-- A COUNTING QUORUM IS NOT AN ADMISSIBLE ORACLE.  `_⊆_` is set inclusion, so
-- `a ∷ a ∷ [] ⊆ a ∷ []`: "at least two blobs" is not `⊆`-monotone and cannot
-- satisfy `CertifiesMono`.  The admissible stricter oracle is the two-voter
-- quorum of `CertSoundBad.certifies₂` (campaign ledger, gotcha 9).
--
-- THE DISCIPLINE IS ENDPOINT-AGNOSTIC — READ THIS BEFORE ANY SYSTEM LIFT.
-- `certMints` mints on `store _ _ stPutVote` and `certNeeds` fires at
-- `store _ _ stCert` for EVERY link and direction; nothing in the key, the
-- mints or the gate says WHOSE store was written or whose certified.  The
-- "at that node" wording above is licensed only because the theorem is
-- stated of ONE node: inside `nodeP n (nodeLogicL n st₀)` the only `store`
-- channels that occur are the `homeOf n` ones — every thread and every store
-- is built from `putVoteEv n` / `certEv n`, and no peer of the bundle offers
-- a `store` channel at all (that is exactly what `ooKA`/`ooCS`/`ooBF`/`ooTS`/
-- `ooLNP`/`ooLFP` establish).  CONSEQUENCE: this discipline does NOT lift to
-- a system of several nodes as it stands — with more than one node's stores
-- in the same composite, a `stPutVote` performed at node X would vouch a
-- `stCert` fired at node Y.  A system-level S3 must first make the key
-- ENDPOINT-INDEXED (mint `(l , d , v)` and gate `stCert` at `(l , d)` on keys
-- carrying that same `(l , d)`); until that is done, no result here may be
-- quoted above node level.  This is the same caveat `VoteSound`'s header
-- records for S2, and for the same reason.
--
-- HOW IT IS PROVED — THE ASSUME-GUARANTEE FRAMEWORK, as in `VoteSound.agda`:
-- `Parametric.BlockProvenance.Carrier` (which carries no `noTick` obligation,
-- so a TERMINATING peer bundle is admissible) and its returning-tree layer
-- `Parametric.BlockProvenanceWfR.Body` (which has `wfR-Prefix`/`wfR-Output`/
-- `wfR-□`/`wf-loop`, so a gate that opens in the middle of a loop body is
-- expressible).  `wf→osafe` is the one bridge back to `OriginSafe`.  The
-- shared leaves — both `Sep`s, the vacuous leaf and BOTH peer bundles, the
-- PROTOTYPE `…P` one included — come from `OriginLeaves.Generic.Leaves`,
-- into which Task 7 hoisted the nine `…P` facts `VoteSound` used to hold.
--
-- WHY S3 SITS ON THE OTHER SIDE OF THE NODE FROM S2.  The gated label
-- `stCert` is EMITTED BY A STORE (`NodeLogicL.voteStore`, through
-- `certify`) and merely absorbed by a thread (`certSink`, which accepts
-- EVERY hash).  So, at `∥⇘ storeES ⇙`:
--
--   * the THREAD side takes the EMPTY guarantee alphabet and is discharged
--     by `OriginLeaves.wf-∅` in one line — all twenty threads, the voter
--     and the LeiosFetch client included.  This is the exact mirror image
--     of S2, where the stores were free and the threads carried the gate;
--   * the STORE side takes the FULL alphabet, and the vote store carries a
--     genuinely non-trivial loop invariant, `InvV ms (bs , cs) = bs ⊆ ms`:
--     every blob the store holds was minted by the deposit that put it
--     there.  `insertU-⊆-cons` maintains it across a deposit and
--     `CertifiesMono` spends it at the firing — `certifies bs r ≡ true`
--     (the guard of `certify`) plus `bs ⊆ ms` gives `certifies ms r ≡ true`
--     (the gate).  This is the campaign's first non-trivial `InvA`;
--   * `Sep storeES ∅α fullα` is vacuous, because the only key-carrying
--     channel is `store … stCert`, which is INSIDE `storeES`.
--
-- The price of the store side is that the four OTHER stores must now be
-- traversed structurally (they are on the full alphabet too, and
-- `_⦀_` forces one alphabet across the group).  `wfR-offerIx`,
-- `wfR-offerHeld`, `wfR-offerBodies`, `wfR-offerTxs` and `wfR-offerCerts`
-- below are that traversal.
--
-- WRITE-UP RULES, IN ONE PLACE.  (1) S3 is not a validity statement.  (2) S3
-- carries a premise; S2 does not.  (3) The positive theorem is
-- ∀-`Params`/∀-`LeiosParams`-with-`CertifiesMono`/∀-topology/∀-node at NODE
-- level, and `CertSoundBad.certSound-node-FAILS` is one node of one concrete
-- instance over a REDUCED composite — never state the two in one sentence.
-- (4) S3 is purely safety-shaped: no module exhibits a good node actually
-- reaching `stCert`.
--
-- ============ WHAT IS STILL FLAGGED FOR A HOIST ============
--
-- Three things here are discipline-independent and belong in
-- `OriginLeaves.agda` the moment a THIRD store-side theorem needs them:
--
--   * `sep-store′ : Sep storeES ∅α fullα` — the MIRROR of
--     `OriginLeaves.sep-store`, which is one-sided (`fullα` on the LEFT).
--     Any theorem whose gated channel is EMITTED by a store needs this
--     one, and its `mem-store` helper is a verbatim copy of the private
--     one inside `OriginLeaves.sep-store`;
--   * `stable-offerIx` / `wfR-offerIx` — generic in the element type, the
--     state type and the channel family, with the "this channel carries
--     nothing" fact taken as a `free` PREMISE.  Reusable as they stand;
--   * `stable-offerHeld`/`wfR-offerHeld`, `stable-offerBodies`/
--     `wfR-offerBodies` and `stable-offerTxs`/`wfR-offerTxs` — NOT generic
--     in the same way: they are about named menu functions of
--     `NodeLogic`/`NodeLogicL` and they HARDWIRE the "carries nothing" fact
--     as `λ ()`, which only reduces because `certNeeds` is empty at
--     `stGet`/`stGetBody`/`stGetTx`.  Hoisting them means giving each a
--     `free` premise too.
--
-- The five `wf-*Store` facts are NOT hoistable: which stores are vacuous
-- depends on which channel the theorem gates, exactly as the thread
-- witnesses do (`OriginLeaves`' header says so).
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Leios.CertSound where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)
open import Class.DecEq.Instances using (DecEq-List)

open import Process_Trees using (AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.Leios.NodeLogicL as NLL
import CSP.Examples.Cardano_network.Parametric.Leios.OriginSafe as OS
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceWfR as BPW
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceSafe as BPS
import CSP.Examples.Cardano_network.Parametric.Leios.OriginLeaves as OL
-- THE SHARED BOOLEAN/LIST LEMMAS.  They live at `VoteSound`'s top level (Task 6) and
-- mention no network parameter; Task 7 deleted this module's own copies of them.
open import CSP.Examples.Cardano_network.Parametric.Leios.VoteSound
  using (∧-split; ∧-join; any-mono)

-- the S3 origin discipline, parametric in the network parameters, the Leios
-- parameters, the topology, the api alphabet and the node-to-voter map — the same
-- five parameters `NodeLogicL.Generic` takes, so `nodeLogicL` below is literally its
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open Params p
    using ( Block; LSlot; VoteBlob; EB; EBHash; RbHash; Tx; TxHash
          ; ebHash; rbHash; txHash; announcedEB
          ; decBlock; decEBHash; decLSlot; decVoteBlob; decEB
          ; decRbHash; decTx; decTxHash )
  open LeiosP p using (DecEq-LeiosPoint)
  open LeiosP.LeiosParams lp using (certifies; blobRb)
  open N p
    using ( Link; Net_Api; Net_Api-≟; StoreTag; StoreCar
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; apiLP; store; env; break
          ; stPut; stGet; stGetAt; stPutEB; stGetEBAt; stPutBody; stGetBody
          ; stPutTx; stGetTxAt; stGetTx; stPutVote; stGetVoteAt; stCert; stHasCert )
  -- `Tx`/`TxHash` come from `Params`; `Data.DecEq-Tx` is deliberately NOT opened, so
  -- `decTx` is the ONE `DecEq Tx` in scope and instance search resolves exactly the term
  -- `NodeLogicL` used (ledger gotcha 4) — `VoteSound.Generic` does the same.
  open D p using (Payload)
  -- (wholesale, as `NetworkPar` and `OriginLeaves`: `Dir` and the six `IDs`)
  open import CSP.Examples.Cardano_network.Base
  open Topology t using (Node)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (EventSet; _⦀_; _∥⇘_⇙_)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES
    using (Proc; nodeWith)
  -- the PROTOTYPE peer bundle, the selector for every theorem on this branch
  open import CSP.Examples.Cardano_network.Parametric.Leios.PeersP p using (nodeBundleP)
  open import Semantics.LTS
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; √; evLabel)
  open import Semantics.Failures
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⊑T_)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using (NoRet; NoRet-Par; NoRet-⦀; NoRet-loop0)
  -- the right-sided `NoRet`: a node puts its TERMINATING peer bundle on the LEFT of
  -- `∥⇘ apiES ⇙`, and `DRCongruenceRep.NoRet-Par` reads the left operand.  Already
  -- proved, at this very telescope, by the announcement campaign.
  open BPS.Generic p t apiES using (NoRet-ParR)
  open NL.Generic p t apiES using (Held; storeES; offerHeld)
  open NLL.Generic p lp t apiES voterOf
    using ( nodeLogicL; st₀; DecEq-⊤poly; DecEq-Votes
          ; Entries; Bodies; Mem; Blobs; Certs; Votes
          ; memberOf; insertU; offerIx
          ; getAtEv; putEBEv; getEBAtEv; putBodyEv; getBodyEv
          ; putTxEv; getTxAtEv; getTxEv; putVoteEv; getVoteAtEv; certEv; hasCertEv
          ; storeStepL; blockStoreL; ebStep; ebStore; bodyStep; offerBodies; bodyStore
          ; memStep; offerTxs; mempool; certify; offerCerts; voteStep; voteStore )
  open OS.Generic p t apiES using (noRet→noTick)

  ------------------------------------------------------------------------
  -- The origin discipline
  ------------------------------------------------------------------------

  -- THE KEY IS THE VOTE BLOB ITSELF.  The certification oracle reads a LIST OF BLOBS,
  -- not hashes, so the minted set has to be exactly the list of blobs deposited.
  Minted : Set
  Minted = List VoteBlob

  -- THE RANKING-BLOCK HASHES A LABEL NEEDS CERTIFIED before it may fire: one for a
  -- certificate, none anywhere else.  A certificate names an RB, not an EB — the
  -- prototype's vote endorses the RANKING BLOCK (spec §4.1) — so the key type is
  -- `RbHash`.  The gate, the carrying relation of the assume-guarantee instance and
  -- every peer's confinement are all read off THIS list, so the channel enumeration is
  -- paid once (`needs-store`).
  certNeeds : (at : AnyTypes (Net_Api Payload)) → proj₁ at → List RbHash
  certNeeds (_ , store _ _ stCert) r = r ∷ []
  certNeeds _                      _ = []

  -- WHAT MINTS: depositing a vote blob.  Nothing else adds to the oracle's input.
  -- ENDPOINT-AGNOSTIC (link and direction are `_`) — see the module header before
  -- lifting any of this above node level.
  certMints : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Minted
  certMints (_ , store _ _ stPutVote) v = v ∷ []
  certMints _                         _ = []

  -- are all the RB hashes the label needs certified by the blobs minted so far?
  allCert : List RbHash → Minted → Bool
  allCert rs ms = all (certifies ms) rs

  -- every hash certified gives the Boolean conjunction …
  allCert⁺ : ∀ rs ms → (∀ {r} → r ∈ rs → certifies ms r ≡ true) → allCert rs ms ≡ true
  allCert⁺ []       ms f = refl
  allCert⁺ (x ∷ rs) ms f = ∧-join (f (here refl)) (allCert⁺ rs ms (λ q → f (there q)))

  -- … and back
  allCert⁻ : ∀ rs ms → allCert rs ms ≡ true → ∀ {r} → r ∈ rs → certifies ms r ≡ true
  allCert⁻ (x ∷ rs) ms eq (here refl) = proj₁ (∧-split eq)
  allCert⁻ (x ∷ rs) ms eq (there q)   = allCert⁻ rs ms (proj₂ (∧-split eq)) q

  -- WHAT IS GATED: a label may fire only when the oracle certifies every RB hash it
  -- names against the blobs minted so far.  Only a certificate names one.
  certGate : Minted → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool
  certGate ms at a = allCert (certNeeds at a) ms

  -- A MONOTONE CERTIFICATION ORACLE: more blobs never WITHDRAW a certificate.  A
  -- hypothesis about the oracle, not about the logic (module header).  It is an ALIAS
  -- for `LeiosParams.CertifiesMono lp`, so the two are interchangeable at an instance by
  -- definition and cannot drift apart.  A COUNTING quorum is inadmissible: `[a,a] ⊆ [a]`.
  CertifiesMono : Set
  CertifiesMono = LeiosP.CertifiesMono p lp

  ------------------------------------------------------------------------
  -- The assume-guarantee data
  ------------------------------------------------------------------------

  -- WHICH LABEL CARRIES WHICH RB HASH: a certificate carries the hash it names, and
  -- nothing else carries anything.  `Carries` and the gate are the same list.
  certCarries : (at : AnyTypes (Net_Api Payload)) → proj₁ at → RbHash → Set
  certCarries at a r = r ∈ certNeeds at a

  -- the payload predicate: the oracle certifies the RB hash against what has been minted
  certWA : Minted → RbHash → Set
  certWA ms r = certifies ms r ≡ true

  -- the minted set a label leads to: EXACTLY `OriginSafe`'s `mintedAfter` on a visible
  -- label, and unchanged on a τ or a `√`.  This equation is what makes the bridge a
  -- five-liner.
  certNext : Label (⊤ {0ℓ}) → Minted → Minted
  certNext (ev (evl (evLabel X e a))) ms = certMints (X , e) a ++ ms
  certNext _                          ms = ms

  -- the minted set only grows
  certNext-⊆ : ∀ a ms → ms ⊆ certNext a ms
  certNext-⊆ (ev (evl (evLabel X e a))) ms = ∈-++⁺ʳ (certMints (X , e) a)
  certNext-⊆ (ev (√ _))                 ms = λ q → q
  certNext-⊆ τ                          ms = λ q → q

  ------------------------------------------------------------------------
  -- The ONE alphabet enumeration
  ------------------------------------------------------------------------

  -- ONLY A CERTIFICATE NEEDS A HASH.  32 clauses — the 18 non-`store` `Net_Api`
  -- constructors plus `store` expanded over all 14 `StoreTag`s — because `certNeeds`'
  -- catch-all does not reduce until the constructor is known.  Everything
  -- channel-shaped below goes through this.
  needs-store : ∀ {X} {e : Net_Api Payload X} {a : X} {r} → certCarries (X , e) a r
              → Σ[ l ∈ Link ] Σ[ d ∈ Dir ] Σ[ m ∈ StoreTag ]
                  (_≡_ {A = AnyTypes (Net_Api Payload)}
                       (X , e) (StoreCar m , store l d m))
  needs-store {e = store l d stCert}          _  = l , d , stCert , refl
  needs-store {e = store _ _ stPut}           ()
  needs-store {e = store _ _ stGet}           ()
  needs-store {e = store _ _ (stGetAt _)}     ()
  needs-store {e = store _ _ stPutEB}         ()
  needs-store {e = store _ _ (stGetEBAt _)}   ()
  needs-store {e = store _ _ stPutBody}       ()
  needs-store {e = store _ _ (stGetBody _)}   ()
  needs-store {e = store _ _ stPutTx}         ()
  needs-store {e = store _ _ (stGetTxAt _)}   ()
  needs-store {e = store _ _ stPutVote}       ()
  needs-store {e = store _ _ (stGetVoteAt _)} ()
  needs-store {e = store _ _ (stGetTx _)}     ()
  needs-store {e = store _ _ (stHasCert _)}   ()
  needs-store {e = input _ _ _}               ()
  needs-store {e = output _ _ _}              ()
  needs-store {e = sndmsg _ _ _}              ()
  needs-store {e = rcvmsg _ _ _}              ()
  needs-store {e = tx _ _ _}                  ()
  needs-store {e = sndack _ _ _}              ()
  needs-store {e = rcvack _ _ _}              ()
  needs-store {e = ack _ _ _}                 ()
  needs-store {e = done _ _ _}                ()
  needs-store {e = apiCS _ _ _}               ()
  needs-store {e = apiBF _ _ _}               ()
  needs-store {e = apiTS _ _ _}               ()
  needs-store {e = apiKA _ _ _}               ()
  needs-store {e = apiLN _ _ _}               ()
  needs-store {e = apiLF _ _ _}               ()
  needs-store {e = apiLP _ _ _}               ()
  needs-store {e = env _ _ _}                 ()
  needs-store {e = break _}                   ()

  -- THE SHARED LEAVES: the vacuous-leaf lemmas at both carriers, the two guarantee
  -- alphabets and their `Sep`s, and the whole peer bundle — none of which depends on
  -- WHICH store channel is gated
  open OL.Generic.Leaves p t apiES Minted RbHash certCarries certWA certNext
                         _⊆_ ⊆-refl ⊆-trans certNext-⊆ needs-store

  -- the assume-guarantee carrier at the S3 discipline …
  open BP.Carrier (Net_Api-≟ {Payload}) Minted RbHash certCarries certWA
                  certNext _⊆_ ⊆-trans certNext-⊆
    using (Wf; nowW; stepW; wf-mono-G; Sep; wf-Par; wf-⦀)

  -- … and its returning-tree layer, at the SAME arguments, so the two `Wf`s are the
  -- same record
  open BPW.Body (Net_Api-≟ {Payload}) Minted RbHash certCarries certWA
                certNext _⊆_ ⊆-refl ⊆-trans certNext-⊆
    using ( WfR; Stable; stable-node; stable-□
          ; wfR-Ret; wfR-Stop; wfR-Prefix; wfR-Output; wfR-□; wf-loop )

  ------------------------------------------------------------------------
  -- THE STORE MENUS
  --
  -- The three read menus of `NodeLogicL`, each a right-nested `□` chain of outputs
  -- ending in `Stop`.  None of their channels is `stCert`, so every `OK` obligation
  -- dies on an empty `certNeeds`; what the chain costs is the induction and the
  -- `Stable` witness `wfR-□` demands of both operands.
  ------------------------------------------------------------------------

  -- a read-pointer menu is stable: every operand is a bare output, and `Stop` is a
  -- `react` with no τ
  stable-offerIx : ∀ {A St : Set} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq St ⦄
                     (ch : ℕ → Net_Api Payload A) (xs : List A) (k : ℕ) (st : St)
                 → Stable (offerIx ch xs k st)
  stable-offerIx ch []       k st = stable-node refl
  stable-offerIx ch (x ∷ xs) k st =
    stable-□ (stable-node refl) (stable-offerIx ch xs (suc k) st)

  -- … and well-formed whenever none of its channels carries a hash, since it hands
  -- back the state it was given
  wfR-offerIx : ∀ {A St : Set} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq St ⦄
                  {Inv : Minted → St → Set} {ms}
                  (ch : ℕ → Net_Api Payload A) (xs : List A) (k : ℕ) (st : St)
              → (∀ i (x : A) {h} → certCarries (A , ch i) x h → ⊥)
              → (∀ {s₁ s₂} → s₁ ⊆ s₂ → Inv s₁ st → Inv s₂ st)
              → Inv ms st
              → WfR fullα ms Inv (offerIx ch xs k st)
  wfR-offerIx ch []       k st free mono inv = wfR-Stop
  wfR-offerIx ch (x ∷ xs) k st free mono inv =
    wfR-□ _ _ (stable-node refl) (stable-offerIx ch xs (suc k) st)
      (wfR-Output (λ _ _ c → ⊥-elim (free k x c))
                  (λ le _ → wfR-Ret (λ le′ →
                     mono (⊆-trans le (⊆-trans (certNext-⊆ _ _) le′)) inv)))
      (wfR-offerIx ch xs (suc k) st free mono inv)

  -- the RB store's legacy offer menu is stable …
  stable-offerHeld : ∀ n (held hs : Held) → Stable (offerHeld n held hs)
  stable-offerHeld n held []       = stable-node refl
  stable-offerHeld n held (b ∷ bs) =
    stable-□ (stable-node refl) (stable-offerHeld n held bs)

  -- … and carries nothing: `stGet` is not `stCert`
  wfR-offerHeld : ∀ {ms} n (held hs : Held)
                → WfR fullα ms (λ _ _ → ⊤ {0ℓ}) (offerHeld n held hs)
  wfR-offerHeld n held []       = wfR-Stop
  wfR-offerHeld n held (b ∷ bs) =
    wfR-□ _ _ (stable-node refl) (stable-offerHeld n held bs)
      (wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt)))
      (wfR-offerHeld n held bs)

  -- the body store's by-hash menu is stable …
  stable-offerBodies : ∀ n (bs ebs : Bodies) → Stable (offerBodies n bs ebs)
  stable-offerBodies n bs []         = stable-node refl
  stable-offerBodies n bs (eb ∷ ebs) =
    stable-□ (stable-node refl) (stable-offerBodies n bs ebs)

  -- … and carries nothing either
  wfR-offerBodies : ∀ {ms} n (bs ebs : Bodies)
                  → WfR fullα ms (λ _ _ → ⊤ {0ℓ}) (offerBodies n bs ebs)
  wfR-offerBodies n bs []         = wfR-Stop
  wfR-offerBodies n bs (eb ∷ ebs) =
    wfR-□ _ _ (stable-node refl) (stable-offerBodies n bs ebs)
      (wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt)))
      (wfR-offerBodies n bs ebs)

  -- the mempool's BY-HASH menu is stable …
  stable-offerTxs : ∀ n (ts us : Mem) → Stable (offerTxs n ts us)
  stable-offerTxs n ts []          = stable-node refl
  stable-offerTxs n ts (tx′ ∷ us)  =
    stable-□ (stable-node refl) (stable-offerTxs n ts us)

  -- … and carries nothing: `stGetTx` is not `stCert`, and it hands the mempool back
  wfR-offerTxs : ∀ {ms} n (ts us : Mem)
               → WfR fullα ms (λ _ _ → ⊤ {0ℓ}) (offerTxs n ts us)
  wfR-offerTxs n ts []         = wfR-Stop
  wfR-offerTxs n ts (tx′ ∷ us) =
    wfR-□ _ _ (stable-node refl) (stable-offerTxs n ts us)
      (wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt)))
      (wfR-offerTxs n ts us)

  ------------------------------------------------------------------------
  -- THE FOUR STORES THAT NEED NO HASH
  --
  -- On the FULL alphabet, because `_⦀_` forces one alphabet across the store group
  -- and the vote store needs it.  Each is a `loop` whose body is a `□` chain of
  -- prefixes, outputs and menus on channels other than `stCert`.
  ------------------------------------------------------------------------

  -- the RB store: forge, THE CERTIFICATE FORGE RENDEZVOUS, deposit, the legacy menu and
  -- the read-pointer menu.  The `envForgeCert` arm is an `env` channel, so it carries
  -- nothing here for exactly the same reason the `envForge` arm does.
  wf-blockStoreL : ∀ {ms} n (held : Held) → Wf fullα ms (blockStoreL n held)
  wf-blockStoreL n held =
    wf-loop {body = storeStepL n} {a = held} (λ _ _ _ → tt) (λ _ hs _ → body hs) tt
    where
    -- one pass of the RB store
    body : ∀ {s} (hs : Held) → WfR fullα s (λ _ _ → ⊤ {0ℓ}) (storeStepL n hs)
    body hs =
      wfR-□ _ _ (stable-node refl)
        (stable-□ (stable-node refl)
          (stable-□ (stable-node refl)
            (stable-□ (stable-offerHeld n hs hs)
                      (stable-offerIx (getAtEv n) (reverse hs) 0 hs))))
        (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
        (wfR-□ _ _ (stable-node refl)
          (stable-□ (stable-node refl)
            (stable-□ (stable-offerHeld n hs hs)
                      (stable-offerIx (getAtEv n) (reverse hs) 0 hs)))
          (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
          (wfR-□ _ _ (stable-node refl)
            (stable-□ (stable-offerHeld n hs hs)
                      (stable-offerIx (getAtEv n) (reverse hs) 0 hs))
            (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
            (wfR-□ _ _ (stable-offerHeld n hs hs)
                       (stable-offerIx (getAtEv n) (reverse hs) 0 hs)
              (wfR-offerHeld n hs hs)
              (wfR-offerIx (getAtEv n) (reverse hs) 0 hs
                           (λ _ _ ()) (λ _ _ → tt) tt))))

  -- the EB-entry store: a deposit and a read-pointer menu
  wf-ebStore : ∀ {ms} n (es : Entries) → Wf fullα ms (ebStore n es)
  wf-ebStore n es =
    wf-loop {body = ebStep n} {a = es} (λ _ _ _ → tt) (λ _ xs _ → body xs) tt
    where
    -- one pass of the EB-entry store
    body : ∀ {s} (xs : Entries) → WfR fullα s (λ _ _ → ⊤ {0ℓ}) (ebStep n xs)
    body xs =
      wfR-□ _ _ (stable-node refl) (stable-offerIx (getEBAtEv n) xs 0 xs)
        (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
        (wfR-offerIx (getEBAtEv n) xs 0 xs (λ _ _ ()) (λ _ _ → tt) tt)

  -- the EB-body store: a deposit and the by-hash menu
  wf-bodyStore : ∀ {ms} n (bs : Bodies) → Wf fullα ms (bodyStore n bs)
  wf-bodyStore n bs =
    wf-loop {body = bodyStep n} {a = bs} (λ _ _ _ → tt) (λ _ xs _ → body xs) tt
    where
    -- one pass of the EB-body store
    body : ∀ {s} (xs : Bodies) → WfR fullα s (λ _ _ → ⊤ {0ℓ}) (bodyStep n xs)
    body xs =
      wfR-□ _ _ (stable-node refl) (stable-offerBodies n xs xs)
        (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
        (wfR-offerBodies n xs xs)

  -- the mempool: a deposit, THE SUBMISSION RENDEZVOUS, a read-pointer menu and the
  -- by-hash menu.  The `envSubmit` arm is an `env` channel and carries nothing.
  wf-mempool : ∀ {ms} n (ts : Mem) → Wf fullα ms (mempool n ts)
  wf-mempool n ts =
    wf-loop {body = memStep n} {a = ts} (λ _ _ _ → tt) (λ _ xs _ → body xs) tt
    where
    -- one pass of the mempool
    body : ∀ {s} (xs : Mem) → WfR fullα s (λ _ _ → ⊤ {0ℓ}) (memStep n xs)
    body xs =
      wfR-□ _ _ (stable-node refl)
        (stable-□ (stable-node refl)
          (stable-□ (stable-offerIx (getTxAtEv n) xs 0 xs) (stable-offerTxs n xs xs)))
        (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
        (wfR-□ _ _ (stable-node refl)
          (stable-□ (stable-offerIx (getTxAtEv n) xs 0 xs) (stable-offerTxs n xs xs))
          (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
          (wfR-□ _ _ (stable-offerIx (getTxAtEv n) xs 0 xs) (stable-offerTxs n xs xs)
            (wfR-offerIx (getTxAtEv n) xs 0 xs (λ _ _ ()) (λ _ _ → tt) tt)
            (wfR-offerTxs n xs xs)))

  ------------------------------------------------------------------------
  -- THE CONTENT-BEARING LEAF: the vote store
  ------------------------------------------------------------------------

  -- THE CARRIED INVARIANT: every blob the vote store holds was minted by the
  -- `stPutVote` that deposited it.  This is the campaign's first non-trivial loop
  -- invariant — S2 ran `InvA = λ _ _ → ⊤` throughout.
  InvV : Minted → Votes → Set
  InvV ms v = proj₁ v ⊆ ms

  -- a dedup insert of a freshly minted blob keeps the invariant: the old blobs are
  -- minted by hypothesis and the new one is minted by the very deposit
  insertU-⊆-cons : ∀ (v : VoteBlob) (bs ms : Minted)
                 → bs ⊆ ms → insertU v bs ⊆ (v ∷ ms)
  insertU-⊆-cons v bs ms sub with memberOf v bs
  ... | true  = λ q → there (sub q)
  ... | false = f
    where
    -- the appended list: an old blob, or the new one at the end
    f : (bs ++ (v ∷ [])) ⊆ (v ∷ ms)
    f q with ∈-++⁻ bs q
    ... | inj₁ old        = there (sub old)
    ... | inj₂ (here refl) = here refl

  -- THE CERTIFICATE MENU is stable: every operand is a value-free prefix on
  -- `store … stHasCert`, and `Stop` is a `react` with no τ
  stable-offerCerts : ∀ n (vs : Votes) (rs : Certs) → Stable (offerCerts n vs rs)
  stable-offerCerts n vs []       = stable-node refl
  stable-offerCerts n vs (r ∷ rs) =
    stable-□ (stable-node refl) (stable-offerCerts n vs rs)

  -- … and well-formed under the carried invariant: `stHasCert` needs nothing certified
  -- and hands the vote store's state straight back, so `bs ⊆ ms` survives the pass
  wfR-offerCerts : ∀ {ms} n (vs : Votes) (rs : Certs) → InvV ms vs
                 → WfR fullα ms InvV (offerCerts n vs rs)
  wfR-offerCerts n vs []       inv = wfR-Stop
  wfR-offerCerts n vs (r ∷ rs) inv =
    wfR-□ _ _ (stable-node refl) (stable-offerCerts n vs rs)
      (wfR-Prefix (λ _ _ _ ()) (λ le _ _ → wfR-Ret (λ le′ →
         ⊆-trans inv (⊆-trans le le′))))
      (wfR-offerCerts n vs rs inv)

  ------------------------------------------------------------------------

  -- the module the monotonicity premise buys: the specification, the leaves that
  -- spend it, and the theorem
  module Sound (certMono : CertifiesMono) where

    -- MINTING ONLY EVER OPENS THE GATE — PROVIDED THE ORACLE IS MONOTONE.  This is
    -- the one place `CertifiesMono` is spent besides the vote store's firing.
    certGate-mono : ∀ {ms ms′} → ms ⊆ ms′
                  → ∀ at a → certGate ms at a ≡ true → certGate ms′ at a ≡ true
    certGate-mono {ms} {ms′} sub at a eq =
      allCert⁺ (certNeeds at a) ms′
               (λ q → certMono sub _ (allCert⁻ (certNeeds at a) ms eq q))

    -- the generic carrier at the S3 discipline.  `OriginSpecT` is renamed rather than
    -- listed: Agda rejects a name that appears in both `using` and `renaming`.
    open OS.Generic.Origin p t apiES VoteBlob decVoteBlob certMints certGate certGate-mono
      using ( mintedAfter; mintedAfter-⊇; originOffer; OriginSpecAt; specAt-init
            ; OSafe; gateOK; onτ; onEv; noTick; osafe→⊑T )
      renaming (OriginSpecT to CertSpecT)
      public

    ------------------------------------------------------------------------
    -- THE BRIDGE
    ------------------------------------------------------------------------

    -- A `Wf` FACT ON THE FULL ALPHABET IS AN `OSafe` FACT.  The two carriers agree by
    -- construction: `certNext` on a visible label IS `mintedAfter`, `OK` at a label IS
    -- the gate (`allCert⁺`), and `Wf` on `fullα` guarantees it for every label.  The
    -- one thing `Wf` does not carry is `OSafe`'s `noTick`, which comes from `NoRet`.
    wf→osafe : ∀ {ms} {M : Proc} → Wf fullα ms M → NoRet M → OSafe ms M
    wf→osafe {ms = ms} w nr .gateOK {e = e} {a = a} st =
      allCert⁺ (certNeeds (_ , e) a) ms (nowW w ⊆-refl tt st)
    wf→osafe w nr .onτ    st = wf→osafe (stepW w ⊆-refl st tt) (NoRet.stepNR nr st)
    wf→osafe w nr .onEv   st =
      wf→osafe (stepW w ⊆-refl st (nowW w ⊆-refl tt st)) (NoRet.stepNR nr st)
    wf→osafe w nr .noTick st = noRet→noTick nr st

    ------------------------------------------------------------------------
    -- The vote store
    ------------------------------------------------------------------------

    -- THE FIRING.  `certify` offers `stCert ! h` only under the Boolean guard
    -- `certifies bs h ∧ not (memberOf h cs)`; its left conjunct plus the carried
    -- `bs ⊆ ms` and `CertifiesMono` give the gate, `certifies ms h ≡ true`.
    wfR-certify : ∀ n {ms} (bs : Blobs) (cs : Certs) (r : RbHash)
                → bs ⊆ ms → WfR fullα ms InvV (certify n bs cs r)
    wfR-certify n bs cs r sub with certifies bs r ∧ not (memberOf r cs) in eq
    ... | false = wfR-Ret (λ le → ⊆-trans sub le)
    ... | true  =
      wfR-Output (λ le _ → λ { (here refl) → certMono (λ q → le (sub q)) r
                                                      (proj₁ (∧-split eq))
                             ; (there ()) })
                 (λ le _ → wfR-Ret (λ le′ → ⊆-trans sub (⊆-trans le le′)))

    -- one pass of the vote store: a deposit — which mints the blob, dedup-inserts it
    -- and consults the oracle — or the read-pointer menu
    wfR-voteStep : ∀ n {ms} (vs : Votes) → InvV ms vs → WfR fullα ms InvV (voteStep n vs)
    wfR-voteStep n (bs , cs) inv =
      wfR-□ _ _ (stable-node refl)
        (stable-□ (stable-offerIx (getVoteAtEv n) bs 0 (bs , cs))
                  (stable-offerCerts n (bs , cs) cs))
        (wfR-Prefix (λ _ _ _ ()) (λ le v _ →
           wfR-certify n (insertU v bs) cs _ (insertU-⊆-cons v bs _ (⊆-trans inv le))))
        (wfR-□ _ _ (stable-offerIx (getVoteAtEv n) bs 0 (bs , cs))
                   (stable-offerCerts n (bs , cs) cs)
          (wfR-offerIx (getVoteAtEv n) bs 0 (bs , cs)
                       (λ _ _ ()) (λ le iv → ⊆-trans iv le) inv)
          (wfR-offerCerts n (bs , cs) cs inv))

    -- THE VOTE STORE: the loop, under the carried invariant
    wf-voteStore : ∀ {ms} n (vs : Votes) → InvV ms vs → Wf fullα ms (voteStore n vs)
    wf-voteStore n vs inv =
      wf-loop {body = voteStep n} {InvA = InvV} {a = vs} (λ le a iv → ⊆-trans iv le)
              (λ _ a iv → wfR-voteStep n a iv) inv

    ------------------------------------------------------------------------
    -- The assembly
    ------------------------------------------------------------------------

    -- SEP AT THE STORE RENDEZVOUS, THE OTHER WAY ROUND.  `OriginLeaves.sep-store` puts
    -- the full alphabet on the LEFT; S3 needs it on the RIGHT, because the gated
    -- channel is emitted by a store.  Both halves are vacuous for the same reason: a
    -- carrying channel is a `store` channel, hence inside `storeES`.
    sep-store′ : Sep storeES ∅α fullα
    sep-store′ = (λ _ ()) , (λ c _ ¬m → ⊥-elim (¬m (mem-store c)))
      where
      -- a carrying channel is a store channel, and every store channel is in `storeES`
      mem-store : ∀ {X} {e : Net_Api Payload X} {a : X} {h} → certCarries (X , e) a h
                → EventSet.mem storeES (X , e) a
      mem-store c with needs-store c
      ... | _ , _ , _ , refl = tt

    -- THE FIVE STORES, on the full alphabet, at ANY state of the four vacuous ones and
    -- at an EMPTY blob list in the vote store — which is what `InvV ms ([] , cs)` asks
    -- for at every `ms`.  The four states are arguments so that `CertSoundBad`'s SEEDED
    -- composite is assembled by this very lemma.
    wf-stores : ∀ {ms} n (held : Held) (es : Entries) (bs : Bodies) (ts : Mem) (cs : Certs)
              → Wf fullα ms (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀
                               (mempool n ts ⦀ voteStore n ([] , cs)))))
    wf-stores n held es bs ts cs =
      wf-⦀ (wf-blockStoreL n held)
        (wf-⦀ (wf-ebStore n es)
        (wf-⦀ (wf-bodyStore n bs)
        (wf-⦀ (wf-mempool n ts) (wf-voteStore n ([] , cs) (λ ())))))

    -- A GATE-CARRYING STORE GROUP AGAINST ANY THREAD GROUP.  The stores carry the gate,
    -- the threads guarantee nothing — the exact mirror of S2 — and `Sep` asks the
    -- threads for nothing because the gated channel is inside `storeES`.  Stated for an
    -- ARBITRARY thread and store operand so that `CertSoundBad`'s reduced composite is
    -- assembled by the same lemma.
    wf-withThreads : ∀ {ms} {th st : Proc} → Wf fullα ms st
                   → Wf fullα ms (th ∥⇘ storeES ⇙ st)
    wf-withThreads w = wf-mono-G (λ _ _ _ → inj₂ tt) (wf-Par storeES sep-store′ wf-∅ w)

    -- THE NODE LOGIC, at the shipped store group
    wf-logic : ∀ {ms} n → Wf fullα ms (nodeLogicL n st₀)
    wf-logic n = wf-withThreads (wf-stores n [] [] [] [] [])

    -- the node logic never returns — its forge thread is a `loop0` — which is where the
    -- composite's `noTick` comes from, the peer bundle having none
    noRet-logic : ∀ n → NoRet (nodeLogicL n st₀)
    noRet-logic n = NoRet-Par storeES (λ _ _ → tt) (NoRet-⦀ NoRet-loop0)

    ------------------------------------------------------------------------
    -- The statement
    ------------------------------------------------------------------------

    -- THE NODE `nodeLogicL` RUNS IN: `Parametric.Node`'s builder at the PROTOTYPE peer
    -- bundle — the same builder `LeiosInstanceL.leiosSystemL` composes the system from,
    -- and not the stock `Parametric.Node.node`
    nodeP : Node → Proc → Proc
    nodeP = nodeWith nodeBundleP

    -- S3 — CERT SOUNDNESS, node-local.  A node running `nodeLogicL` from empty stores
    -- issues no certificate for a RANKING-BLOCK hash the oracle does not grant on the
    -- vote blobs that have been deposited at it.  No validity is asserted: the
    -- prototype's votes carry no verdict at all.  LEVEL: node.  PREMISE:
    -- `CertifiesMono`, the `Sound` telescope's parameter.
    CertSound : Set₁
    CertSound = ∀ (n : Node) → CertSpecT ⊑T nodeP n (nodeLogicL n st₀)

    -- S3 FOR ANY STORE GROUP THAT CARRIES THE GATE AND NEVER RETURNS.  The bundle and
    -- the logic compose on `apiES` at the full guarantee alphabet, and `wf→osafe` then
    -- `osafe→⊑T` turn that one `Wf` fact into the trace refinement.  The logic is a
    -- PARAMETER so that `CertSoundBad`'s controlled comparison runs through exactly
    -- this assembly.
    soundOf : ∀ n (lg : Proc) → Wf fullα [] lg → NoRet lg → CertSpecT ⊑T nodeP n lg
    soundOf n lg w nr =
      osafe→⊑T (wf→osafe (wf-mono-G (λ _ _ _ → inj₁ tt)
                           (wf-Par apiES sep-api (wf-linkBundlesP n) w))
                         (NoRet-ParR apiES nr))

    -- S3, PROVED (under `CertifiesMono`), at the shipped node logic from empty stores
    certSound : CertSound
    certSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)


------------------------------------------------------------------------
-- THE SHIPPED LINEAR-LEIOS LINE: the premise, DISCHARGED
--
-- `certSound` above is conditional on `CertifiesMono`, so on its own it does not
-- say anything about a RUNNING system.  `LeiosInstanceL.leiosLP`'s oracle — "some
-- held blob names that RB" — IS monotone (`any` is `⊆`-monotone), and `certMonoL`
-- below says so, which turns S3 into an unconditional statement about every node of
-- `LeiosInstanceL.leiosSystemL`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import CSP.Examples.Cardano_network.ApiAlphabet leiosLParams using (apiES)

-- S3's discipline at the shipped three-node Linear-Leios line (`voterOf = id`, as
-- `LeiosInstanceL` instantiates it)
module CSL = Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)

-- THE PREMISE, DISCHARGED AT THE SHIPPED ORACLE.  `leiosLP` certifies `r` exactly
-- when SOME held blob names `r`; more blobs never remove that witness.  So S3 is
-- UNCONDITIONAL for the nodes of this instance.
certMonoL : CSL.CertifiesMono
certMonoL sub r eq = any-mono _ sub eq

-- S3's proof module at the shipped line
module CSLS = CSL.Sound certMonoL

-- S3 AT THE SHIPPED INSTANCE, UNCONDITIONALLY: every node of the Linear-Leios line
-- that `LeiosInstanceL.leiosSystemL` composes issues no certificate its own oracle
-- does not grant on the vote blobs deposited at it.  LEVEL: node — this is
-- `certSound` at one `Params`/`LeiosParams`/`Topology`, not a system-level claim, and
-- the endpoint-agnostic caveat in the module header applies to it unchanged.
certSoundL : CSLS.CertSound
certSoundL = CSLS.certSound

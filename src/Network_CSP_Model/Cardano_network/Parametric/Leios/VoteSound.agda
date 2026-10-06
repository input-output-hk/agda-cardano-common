{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S2, VOTE SOUNDNESS on the PROTOTYPE vote
-- model: the origin discipline, the specification it induces, and the
-- theorem at the node.
--
-- WHAT S2 SAYS NOW (spec §7, "the faithful two-sorted mint key").  The
-- prototype's vote blob carries NO VERDICT — it names a voter and the
-- RANKING BLOCK it endorses, nothing else — so S2 is no longer a statement
-- about validity.  It is a statement about WORK DONE: a node deposits a
-- vote blob `v` in its vote store (`store home(n) stPutVote ! v`) only if
--
--   * `apiLP l d lnpRecvVotes ! vs` delivered `v` — a neighbour sent it, and
--     a RELAYED blob is not S2's business (its origin, that some voter
--     really cast it, is S2′); or
--   * the node itself read a ranking block `b` out of its OWN block store
--     (`store home(n) (stGetAt k) ! b`) with `rbHash b ≡ blobRb v`, AND read
--     the body of the EB that `b` announces (`store home(n) (stGetBody h) ! eb`
--     with `announcedEB b ≡ just h`).
--
-- "ITS OWN STORE" IS NOW A FACT ABOUT THE DISCIPLINE, AND THAT IS WHAT LETS
-- IT LIFT.  The minted key is one of the three sorts TOGETHER WITH THE
-- DEPOSIT ENDPOINT it licenses (`VoteKeyE = (Link × Dir) × VoteKey`, so
-- `Minted = List VoteKeyE`), and what a deposit CARRIES is likewise a blob
-- together with the endpoint it is deposited at (`VoteNeed`).  A
-- `store l d (stGetAt k) ! b` mints `((l , d) , kRb b)` and a
-- `store l d (stGetBody h) ! eb` mints `((l , d) , kBody h)` — both
-- node-local, since `getAtEv n`, `getBodyEv n` and `putVoteEv n` all fire at
-- `homeOf n`, so record η closes that half definitionally.  An
-- `apiLP l d lnpRecvVotes ! vs` mints `(homeAt (l , d) , kRelay v)` for each
-- blob, where `homeAt (l , d)` is the home endpoint of the node that OWNS
-- `(l , d)`; a `store l d stPutVote ! v` demands keys carrying that same
-- `(l , d)`, and `voteκ`'s FIRST conjunct is exactly that endpoint test.
-- Since `homeOf` is injective (`homeOf-inj`), a read or a delivery at node X
-- vouches no deposit at node Y, and `Leios.VoteSystemL` spends exactly that.
-- The wire mint has to be NORMALISED to the depositing endpoint rather than
-- keyed by the receiving one, because a node receives at every incident
-- endpoint but deposits only at `homeOf n`; the normalisation is sound because
-- `Topology.endpoints-sound` identifies the owner of `(l , d)`, which the
-- membership-carrying fold `BlockProvenanceWfR.wf-⦀⁺∈` delivers to the one
-- leaf that needs it.
--
-- THE RE-KEYED NODE-LEVEL THEOREM IS **NO WEAKER** THAN THE OLD ONE, and that
-- is the direction that may be quoted.  Whenever the new gate stands open at a
-- deposit, so did the old one: each new disjunct implies the old one at the
-- key's sort — the relay key `((l , d) , kRelay v)` can only have been put
-- there by a delivery of `v`, and the `kRb`/`kBody` witnesses the endpoint
-- test admits are a SUBSET of those the endpoint-blind `any` admitted.  Hence
-- every trace the NEW `VoteSpecT` permits the old one permitted.  The converse
-- is NOT proved here, so "no weaker" is the claim, never "strictly stronger".
--
-- THE SORT IS TWO-SORTED plus a relay sort: `kRb`, `kBody`, `kRelay`.  The
-- endpoint is added as a PRODUCT in front of the sort rather than as an extra
-- argument to each constructor — simpler, it leaves `decVoteKey` untouched,
-- and it matches the shape S1, S2′, S3 and S4 all use.  Both conjuncts of the second clause are needed and neither is
-- derivable from the other: `NodeLogicL.voterBody` walks `held` (it reads an
-- RB, not an EB entry) and BLOCKS at that RB's announced body before it
-- votes, so the discipline mirrors the thread exactly.  Dropping `kBody`
-- would leave the weaker "votes only about held RBs", which is NOT what is
-- shipped here.  `kRelay` cannot be dropped: the Notify client accepts any
-- blob list off the wire, so without it the property is FALSE.
--
-- THE MINT ON A BODY READ TAKES THE HASH FROM THE CHANNEL (`stGetBody h`),
-- not from `ebHash eb` — the emitting thread cannot see the store-side fact
-- `ebHash eb ≡ h`.  The two agree at the composite anyway
-- (`NodeLogicL.offerBodies` offers `stGetBody (ebHash eb) ! eb` and nothing
-- else), so nothing is lost.
--
-- HOW IT IS PROVED — THE ASSUME-GUARANTEE FRAMEWORK, NOT A SECOND CARRIER.
-- `OriginSafe`'s `OSafe` has no structural closure over `Prefix`/`Output`/
-- `_>>=_`/`loop`, and its `noTick` field is refutable of a peer bundle
-- (peers TERMINATE on `done`).  Both problems are already solved, once,
-- by `Parametric.BlockProvenance.Carrier` and its returning-tree layer
-- `Parametric.BlockProvenanceWfR.Body`: `Wf`/`WfR` carry no `noTick`
-- obligation (`wf-Skip`, `wf-deadlock`) and come with `wfR-Prefix`,
-- `wfR-Output`, `wfR-□`, `wfR->>=`, `wf-loop` and `wf-loop0`.  Both are
-- GENERIC in the event functor, the state, the payload and the carrying
-- relation, so S2 is an INSTANCE of them.  S2 needs no rely at all: all
-- three key sources are state-GROWING labels (`next`), not relies.
-- `wf→osafe` at the bottom is the one bridge back to `OriginSafe`.
--
-- ONE ALPHABET ENUMERATION, `needs-store`.  A pattern-matching definition on
-- `AnyTypes` does not reduce until the channel constructor is known, so
-- SOMETHING has to enumerate them: 32 clauses, being the 18 non-`store`
-- `Net_Api` constructors plus `store` expanded over all 14 `StoreTag`s.
-- (The Task-6 brief said 33; 32 is the count the datatypes actually give.)
-- Routing the gate and the carrying relation through the single
-- `Maybe`-valued `isPutVote` reduces that tax to `needs-store` alone —
-- every other channel-shaped obligation is discharged by a two-clause case
-- on that `Maybe`.
--
-- THE PEER BUNDLE IS `PeersP.nodeBundleP`, the PROTOTYPE bundle.  Its NINE
-- `Wf` facts (`RLNP`, `RLFP`, `ooLNP`, `ooLFP`, `wf-clientPeerP`,
-- `wf-serverPeerP`, `wf-slotP`, `wf-nodeBundleP`, `wf-linkBundlesP`) were
-- written here by Task 6 and HOISTED into `OriginLeaves.Generic.Leaves` by
-- Task 7, beside their `…R` siblings, when S3 became the second prototype
-- instance to need them.  They arrive with the `open OL.Generic.Leaves` below.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.VoteSound where

open import Level using (Level; 0ℓ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-map⁺)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (_≟_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq)
import Class.DecEq.Instances as DecEqI

open import Process_Trees using (AnyTypes; ExtI)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Topology using (Topology; opposite)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
open import Class.DecEq.Instances using (DecEq-List)
import Cardano_network.Net as N
import Cardano_network.Data as D
import CSP.Operators as O
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.OriginSafe as OS
import Cardano_network.Parametric.BlockProvenance as BP
import Cardano_network.Parametric.BlockProvenanceWfR as BPW
import Cardano_network.Parametric.BlockProvenanceSafe as BPS
import Cardano_network.Parametric.Leios.OriginLeaves as OL

------------------------------------------------------------------------
-- The reusable Boolean/list lemmas
--
-- AT TOP LEVEL, and not inside `Generic`, because Task 7's S3 imports them
-- verbatim (`CertSound.agda` carries its own copies today, which that task
-- deletes).  None of them mentions the network parameters.
------------------------------------------------------------------------

-- a Boolean disjunction is true only if one side is
∨-split : ∀ {b c} → b ∨ c ≡ true → b ≡ true ⊎ c ≡ true
∨-split {false} eq = inj₂ eq
∨-split {true}  eq = inj₁ refl

-- … a true left disjunct suffices …
∨-inl : ∀ {b c} → b ≡ true → b ∨ c ≡ true
∨-inl refl = refl

-- … and so does a true right one
∨-inr : ∀ {b c} → c ≡ true → b ∨ c ≡ true
∨-inr {false} refl = refl
∨-inr {true}  _    = refl

-- conjunction splits …
∧-split : ∀ {x y} → x ∧ y ≡ true → x ≡ true × y ≡ true
∧-split {true} {true} refl = refl , refl

-- … and rebuilds
∧-join : ∀ {x y} → x ≡ true → y ≡ true → x ∧ y ≡ true
∧-join refl refl = refl

-- the member that made `any` true
any→∈ : ∀ {A : Set} (f : A → Bool) (xs : List A)
      → any f xs ≡ true → Σ[ x ∈ A ] (x ∈ xs × f x ≡ true)
any→∈ f (x ∷ xs) eq with ∨-split {f x} {any f xs} eq
... | inj₁ fx = x , here refl , fx
... | inj₂ r  = proj₁ q , there (proj₁ (proj₂ q)) , proj₂ (proj₂ q)
  where
  -- the member found in the tail
  q = any→∈ f xs r

-- … and back: one passing member makes `any` true
∈→any : ∀ {A : Set} (f : A → Bool) {x : A} {xs : List A}
      → x ∈ xs → f x ≡ true → any f xs ≡ true
∈→any f (here refl) fx = ∨-inl fx
∈→any f (there q)   fx = ∨-inr (∈→any f q fx)

-- `any` IS `⊆`-MONOTONE: the witness in the smaller list is a witness in the larger.
-- UNUSED IN THIS MODULE — it is here only because Task 7's `CertSound` cleanup imports
-- this block wholesale and spends it (`certMonoL`).  Delete it if that cleanup is dropped.
any-mono : ∀ {A : Set} (f : A → Bool) {xs ys : List A}
         → xs ⊆ ys → any f xs ≡ true → any f ys ≡ true
any-mono f {xs} sub eq with any→∈ f xs eq
... | x , q , fx = ∈→any f (sub q) fx

-- a decision about a value and itself always says `yes`
⌊≟⌋-refl : ∀ {A : Set} ⦃ _ : DecEq A ⦄ (x : A) → ⌊ x ≟ x ⌋ ≡ true
⌊≟⌋-refl x with x ≟ x
... | yes _ = refl
... | no ¬q = ⊥-elim (¬q refl)

-- the S2 origin discipline, parametric in the network parameters, the Leios
-- parameters, the topology, the api alphabet and the node-to-voter map — the same
-- five parameters `NodeLogicL.Generic` takes, so `nodeLogicL` below is literally its
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open Params p
    using ( Block; LSlot; VoterId; VoteBlob; EB; EBHash; RbHash; Tx; TxHash; Size
          ; linkConfig; ebHash; rbHash; txHash; slotOf; announcedEB
          ; decBlock; decEBHash; decLSlot; decVoteBlob; decEB
          ; decRbHash; decTx; decTxHash )
  open LeiosP p using (LeiosEb; LeiosPoint; DecEq-LeiosPoint; allOffsets)
  open LeiosP.LeiosParams lp using (mkVoteBlob; blobRb; blobRb-mk; ebTxs; ebSize; rbCert)
  -- EVERY tag named below MUST appear here: an unlisted tag silently becomes a pattern
  -- VARIABLE and the carrier table turns into a stuck term (campaign ledger, gotcha 1).
  open N p
    using ( Link; Net_Api; Net_Api-≟; StoreTag; StoreCar
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; apiLP; store; env; break
          ; stPut; stGet; stGetAt; stPutEB; stGetEBAt; stPutBody; stGetBody
          ; stPutTx; stGetTxAt; stGetTx; stPutVote; stGetVoteAt; stCert; stHasCert
          ; lnpSendRequestNext; lnpSendBlockOffer; lnpSendBlockTxsOffer; lnpSendVotes
          ; lnpRecvBlockAnnouncement; lnpRecvBlockOffer; lnpRecvBlockTxsOffer
          ; lnpRecvVotes
          ; lfpSendBlockRequest; lfpSendBlockTxsRequest; lfpSendBlock; lfpSendBlockTxs
          ; lfpRecvBlock; lfpRecvBlockTxs; lfpReqBlockRequest; lfpReqBlockTxsRequest )
  -- `Tx`/`TxHash` come from `Params` (`Data` re-exports neither, and `txData` is gone);
  -- `DecEq-Tx` is deliberately NOT opened, so `decTx` is the ONE `DecEq Tx` in scope and
  -- instance search resolves exactly the term `NodeLogicL` used (ledger gotcha 4).
  open D p
    using ( Payload; Point; Header; Tip; Vote; point; header; vote; TxBitmap
          ; DecEq-Point; DecEq-Header; DecEq-Tip; DecEq-ChainRange; DecEq-Payload
          ; DecEq-Vote; DecEq-EBPoint; DecEq-TxBitmap; DecEq-TxEntries
          ; DecEq-TxsRequest; DecEq-TxsReply; DecEq-Offer )
  -- (wholesale, as `NetworkPar` and `BlockProvenancePeers`: the `Dir` decidable
  -- equality the peer bundle dispatches on, and the six `IDs` constructors)
  open import Cardano_network.Base
  open Topology t using (Node; endpointsOf; endpointsList; endpoints-sound)
  -- `endAt` is NOT opened: the record's derived `endAt` is a pattern-matching lambda and
  -- the opened copy does not unify with the one inside `endpoints-sound`'s instantiated
  -- type (`BlobOrigin` measured the `UnequalTerms`).  The qualified projection does.
  endAtT : Link → Dir → Node
  endAtT = Topology.endAt t
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (EventSet; Skip; Ret; _⦀_; _∥⇘_⇙_; Prefix; Prefix₀; Output; _□_; _◁_▷_)
  open import Cardano_network.Parametric.Node p t apiES
    using (Proc; nodeWith; bundleAtWith; linkBundlesWith)
  open import Semantics.LTS
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; √; evLabel)
  open import Semantics.Failures
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⊑T_)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using ( OffersOnly; NoRet
          ; OffersOnly-Ret; OffersOnly-Skip; OffersOnly-Prefix; OffersOnly-Prefix₀
          ; OffersOnly-Output; OffersOnly->>=; OffersOnly-loop; OffersOnly-loop0
          ; NoRet-Par; NoRet-⦀; NoRet-loop; NoRet-loop0 )
  -- the right-sided `NoRet`: a node puts its TERMINATING peer bundle on the LEFT of
  -- `∥⇘ apiES ⇙`, and `DRCongruenceRep.NoRet-Par` reads the left operand.  Already
  -- proved, at this very telescope, by the announcement campaign.
  open BPS.Generic p t apiES using (NoRet-ParR)
  open NL.Generic p t apiES
    using (storeES; homeOf; putEv; clientLoop; clientBody-k; serverBody-k)
  open NLL.Generic p lp t apiES voterOf
    using ( nodeLogicL; st₀; DecEq-⊤poly; DecEq-ℕ×ℕ; at?
          ; getAtEv; putEBEv; putBodyEv; getBodyEv; putVoteEv; getVoteAtEv
          ; putTxEv; getTxAtEv; getTxEv; hasCertEv; forgeOK
          ; forgeL; forgeBodyL; forgeCertL
          ; ebIndex; voter; voterBody; submit; certSink
          ; serverLoopL; lnServerLoopL; bodyOfferLoop; voteOfferLoop
          ; ebServeLoop; ebTxsServeLoop; serveTxs; putChecked; tsPull; tsServe; putAllTx
          ; lnClientLoopL; fetchBody; fetchTxs; putAllVotes; awaitTxs
          ; endpointThreadsL; allThreadsL )
    -- `putAllTx`'s own membership test, RENAMED so it cannot be confused with (or
    -- shadowed by) `OriginSafe.memberOf` below: the two are textually identical but
    -- DISTINCT functions, and a `with` on the wrong one leaves the guard's `if` stuck
    renaming (memberOf to memberOfNL)
  open OS using (memberOf; memberOf-mono; ∈→memberOf)
  open OS.Generic p t apiES using (noRet→noTick)
  -- the PROTOTYPE peer bundle (its nine `Wf` facts now live in `OriginLeaves.Leaves`)
  open import Cardano_network.Parametric.Leios.PeersP p using (nodeBundleP)

  ------------------------------------------------------------------------
  -- The origin discipline
  ------------------------------------------------------------------------

  -- THE KEY: the three kinds of fact a vote deposit can appeal to.  A ranking block the
  -- node read out of its OWN block store; an EB body it read out of its OWN body store;
  -- or a blob a neighbour delivered.  (Spec §7's `Block ⊎ EBHash`, plus the relay sort:
  -- without `kRelay` the property is FALSE, because the Notify client accepts any blob
  -- list off the wire and deposits it.)
  data VoteKey : Set where
    kRb    : Block    → VoteKey
    kBody  : EBHash   → VoteKey
    kRelay : VoteBlob → VoteKey

  -- decidable equality of the key: one component decision per diagonal pair, the six
  -- off-diagonal pairs refuted by constructor disjointness
  decVoteKey : (x y : VoteKey) → Dec (x ≡ y)
  decVoteKey (kRb b)    (kRb b′)    with b ≟ b′
  ... | yes refl = yes refl
  ... | no  ¬q   = no λ { refl → ¬q refl }
  decVoteKey (kBody h)  (kBody h′)  with h ≟ h′
  ... | yes refl = yes refl
  ... | no  ¬q   = no λ { refl → ¬q refl }
  decVoteKey (kRelay v) (kRelay v′) with v ≟ v′
  ... | yes refl = yes refl
  ... | no  ¬q   = no λ { refl → ¬q refl }
  decVoteKey (kRb _)    (kBody _)   = no λ ()
  decVoteKey (kRb _)    (kRelay _)  = no λ ()
  decVoteKey (kBody _)  (kRb _)     = no λ ()
  decVoteKey (kBody _)  (kRelay _)  = no λ ()
  decVoteKey (kRelay _) (kRb _)     = no λ ()
  decVoteKey (kRelay _) (kBody _)   = no λ ()

  instance
    -- the key equality the membership gates below need
    DecEq-VoteKey : DecEq VoteKey
    DecEq-VoteKey = record { _≟_ = decVoteKey }

  instance
    -- product `DecEq` for the `sendCSRollForward` carrier (`Header × Tip`) — the same
    -- instance `NodeLogic` declares, so `OffersOnly-Output` sees the one the `!`-output
    -- in `serverBody-k` was built with (`AnnounceSafeLeaves` does the same)
    DecEq-Header×Tip : DecEq (Header × Tip)
    DecEq-Header×Tip = DecEqI.DecEq-×

  ------------------------------------------------------------------------
  -- THE ENDPOINT INDEX, AND THE BOOKKEEPING IT NEEDS
  --
  -- The three sorts stay as they are; the endpoint is added as a PRODUCT in front of
  -- them (`(Link × Dir) × VoteKey`) rather than as an extra argument to each
  -- constructor.  That keeps `decVoteKey` as it is and matches the shape S1/S2′/S3/S4
  -- all use.
  ------------------------------------------------------------------------

  -- the endpoint equality, assembled out of the QUALIFIED `Fin` and `Dir` instances.
  -- Deliberately not an instance declaration: a product instance at this type would
  -- compete with the ones `wfR-Output` resolves its `DecEq X` to (campaign ledger,
  -- gotcha 4).  `CertSound.ld-≟` is the precedent.
  ld-≟ : (x y : Link × Dir) → Dec (x ≡ y)
  ld-≟ = ≡-dec (DecEq._≟_ DecEqI.DecEq-Fin) (DecEq._≟_ DecEq-Dir)

  -- an endpoint decides equal to itself.  `⌊≟⌋-refl` cannot be used: `ld-≟` is not an
  -- instance, by the paragraph above.
  ⌊ld⌋-refl : ∀ (ld : Link × Dir) → ⌊ ld-≟ ld ld ⌋ ≡ true
  ⌊ld⌋-refl ld with ld-≟ ld ld
  ... | yes _  = refl
  ... | no  ¬q = ⊥-elim (¬q refl)

  -- THE MINTED KEY: one of the three sorts TOGETHER WITH THE DEPOSIT ENDPOINT it
  -- licenses.  The endpoint index is what makes the discipline sound at a composite of
  -- SEVERAL nodes: without it a store read at node X would vouch a deposit at node Y.
  VoteKeyE : Set
  VoteKeyE = (Link × Dir) × VoteKey

  -- the key's equality, likewise explicit rather than an instance
  decVoteKeyE : DecEq VoteKeyE
  decVoteKeyE = record { _≟_ = ≡-dec ld-≟ decVoteKey }

  -- is this key in the minted set?  `OriginSafe.memberOf` at the equality above, passed
  -- explicitly because `memberOf` takes its `DecEq` as an INSTANCE argument and
  -- `decVoteKeyE` is not one
  memKey : VoteKeyE → List VoteKeyE → Bool
  memKey k ms = memberOf ⦃ decVoteKeyE ⦄ k ms

  -- … monotone in the minted set, which is what keeps the gate monotone
  memKey-mono : ∀ {k ms ms′} → ms ⊆ ms′ → memKey k ms ≡ true → memKey k ms′ ≡ true
  memKey-mono sub eq = memberOf-mono ⦃ decVoteKeyE ⦄ sub eq

  -- … and implied by propositional membership
  ∈→memKey : ∀ k ms → k ∈ ms → memKey k ms ≡ true
  ∈→memKey k ms q = ∈→memberOf ⦃ decVoteKeyE ⦄ k ms q

  -- `endpoints-sound` with the direction SPLIT FIRST.  The record's derived `endAt` is an
  -- extended lambda, which only reduces at a CONCRETE direction, so the law's conclusion
  -- at an abstract `d` is a stuck term that does not unify with `endAtT l d`.
  sound-at : ∀ n l d → (l , d) ∈ endpointsList n → endAtT l d ≡ n
  sound-at n l lo mem = endpoints-sound n l lo mem
  sound-at n l hi mem = endpoints-sound n l hi mem

  -- a node's HOME endpoint really is its own: `endpoints-sound` at the head of its
  -- incidence list, which is what `NodeLogic.homeOf` picks
  home-own : ∀ n → endAtT (proj₁ (homeOf n)) (proj₂ (homeOf n)) ≡ n
  home-own n = sound-at n (proj₁ (homeOf n)) (proj₂ (homeOf n)) (here refl)

  -- … hence `homeOf` is INJECTIVE: an endpoint belongs to at most one node.  This is the
  -- fact that makes the endpoint-indexed key separate the nodes of one composite.
  homeOf-inj : ∀ {n m} → homeOf n ≡ homeOf m → n ≡ m
  homeOf-inj {n} {m} eq =
    trans (sym (home-own n))
          (trans (cong (λ ld → endAtT (proj₁ ld) (proj₂ ld)) eq) (home-own m))

  -- THE DEPOSIT ENDPOINT A DELIVERY AT ONE ENDPOINT LICENSES: the home endpoint of the
  -- node that owns the receiving endpoint.  A node receives at EVERY endpoint incident to
  -- it but deposits only at `homeOf n` (`NodeLogicL.putVoteEv`), so a mint keyed by the
  -- receiving endpoint itself would licence nothing at a node of degree > 1.
  homeAt : Link × Dir → Link × Dir
  homeAt ld = homeOf (endAtT (proj₁ ld) (proj₂ ld))

  -- WHAT A VOTE DEPOSIT NEEDS JUSTIFYING: the blob TOGETHER WITH THE ENDPOINT it is
  -- deposited at.  This is the `Carries` payload — a different type from the minted key,
  -- as it was before the re-keying (`VoteBlob` against `VoteKey`).
  VoteNeed : Set
  VoteNeed = (Link × Dir) × VoteBlob

  ------------------------------------------------------------------------
  -- The origin discipline, endpoint-indexed
  ------------------------------------------------------------------------

  -- WHAT MINTS.  Reading the k-th oldest held RB mints that RB; reading a body out of
  -- the body store mints THE HASH THE READ ASKED FOR (the store offers `stGetBody h`
  -- only when `ebHash eb ≡ h`, so the two agree at the composite, and this is the form
  -- the emitting thread can prove on its own); a Notify votes reply mints one relay key
  -- per blob delivered.  Everything else mints nothing.  EVERY MINT IS KEYED BY THE
  -- DEPOSIT ENDPOINT IT LICENSES: the two store reads are node-local (`getAtEv n` and
  -- `getBodyEv n` fire at `homeOf n`, which is also where `putVoteEv n` fires), so their
  -- own `(l , d)` is already the right key; the wire delivery is PER-ENDPOINT, so it is
  -- normalised through `homeAt`.
  voteMints : (at : AnyTypes (Net_Api Payload)) → proj₁ at → List VoteKeyE
  voteMints (_ , store l d (stGetAt _))   b  = ((l , d) , kRb b) ∷ []
  voteMints (_ , store l d (stGetBody h)) eb = ((l , d) , kBody h) ∷ []
  voteMints (_ , apiLP l d lnpRecvVotes)  vs =
    map (λ v → (homeAt (l , d) , kRelay v)) vs
  voteMints _                             _  = []

  -- ONE MINTED FACT, TESTED AGAINST A BLOB AT A DEPOSIT ENDPOINT: is it a ranking block
  -- READ AT THAT VERY ENDPOINT whose hash the blob names, and whose announced EB body was
  -- itself read there?  A named function rather than a `where`-bound one, so the leaf
  -- proofs can apply `∈→any` to it by name.
  -- the HASH-AND-BODY half of the test, named: it is what the endpoint conjunct guards,
  -- and having a name for it is what lets the monotonicity proof below pin `∧-split`'s and
  -- `∧-join`'s implicit arguments.  `⌊ ld-≟ ld ld′ ⌋` is a STUCK term at an abstract
  -- endpoint (`≡-dec`'s own `with` does not reduce), so `_∧_` does not reduce either and
  -- an unpinned `∧-split` blocks (measured: four `UnsolvedConstraints`).
  voteRb : List VoteKeyE → Link × Dir → VoteBlob → Block → Bool
  voteRb ms ld v b = ⌊ rbHash b ≟ blobRb v ⌋ ∧
                       maybe′ (λ h → memKey (ld , kBody h) ms) false (announcedEB b)

  voteκ : List VoteKeyE → Link × Dir → VoteBlob → VoteKeyE → Bool
  voteκ ms ld v (ld′ , kRb b)  = ⌊ ld-≟ ld ld′ ⌋ ∧ voteRb ms ld v b
  voteκ ms ld v (_ , kBody _)  = false
  voteκ ms ld v (_ , kRelay _) = false

  -- DID THE NODE ITSELF DO THE WORK BEHIND `v`, AT THIS DEPOSIT ENDPOINT?  Some RB minted
  -- there hashes to `blobRb v` and the body it announces was minted there too.
  ownVote : List VoteKeyE → Link × Dir → VoteBlob → Bool
  ownVote ms ld v = any (voteκ ms ld v) ms

  -- IS THIS DEPOSIT VOUCHED FOR?  Either the blob came off the wire AT THIS VERY DEPOSIT
  -- ENDPOINT, or the node did the work itself there.
  vouched : List VoteKeyE → VoteNeed → Bool
  vouched ms (ld , v) = memKey (ld , kRelay v) ms ∨ ownVote ms ld v

  -- IS THIS THE VOTE-DEPOSIT CHANNEL, AND WITH WHICH BLOB — AND AT WHICH ENDPOINT?  The
  -- ONE catch-all channel dispatch of the discipline: the gate and the carrying relation
  -- both route through it, so each of them is discharged by a two-clause case on this
  -- `Maybe` instead of a thirty-two-clause alphabet enumeration.  (`needs-store` still
  -- writes that enumeration once, because its conclusion is a Σ about the channel itself.)
  isPutVote : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Maybe VoteNeed
  isPutVote (_ , store l d stPutVote) v = just ((l , d) , v)
  isPutVote _                         _ = nothing

  -- WHAT IS GATED: only a vote deposit, and only by `vouched`.  Everything else is free.
  voteGate : List VoteKeyE → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool
  voteGate ms at a = maybe′ (vouched ms) true (isPutVote at a)

  -- the announced-body membership inside `voteκ` is monotone in the minted list
  body-mono : ∀ {ms ms′} → ms ⊆ ms′ → ∀ ld b
            → maybe′ (λ h → memKey (ld , kBody h) ms)  false (announcedEB b) ≡ true
            → maybe′ (λ h → memKey (ld , kBody h) ms′) false (announcedEB b) ≡ true
  body-mono sub ld b q with announcedEB b
  ... | just h  = memKey-mono sub q
  ... | nothing = q

  -- the hash-and-body half is monotone: the hash test does not mention the minted set
  voteRb-mono : ∀ {ms ms′} → ms ⊆ ms′ → ∀ ld v b
              → voteRb ms ld v b ≡ true → voteRb ms′ ld v b ≡ true
  voteRb-mono sub ld v b eq =
    ∧-join (proj₁ (∧-split eq)) (body-mono sub ld b (proj₂ (∧-split eq)))

  -- … and so is the whole test at a `kRb` key, the endpoint conjunct being independent of
  -- the minted set.  ALL THREE IMPLICIT PAIRS ARE PINNED, because `⌊ ld-≟ ld ld′ ⌋` is
  -- stuck and `_∧_` therefore does not reduce.
  voteκ-mono : ∀ {ms ms′} → ms ⊆ ms′ → ∀ ld v ld′ b
             → voteκ ms ld v (ld′ , kRb b) ≡ true → voteκ ms′ ld v (ld′ , kRb b) ≡ true
  voteκ-mono {ms} {ms′} sub ld v ld′ b eq =
    ∧-join {⌊ ld-≟ ld ld′ ⌋} {voteRb ms′ ld v b}
           (proj₁ split) (voteRb-mono sub ld v b (proj₂ split))
    where
    -- the two conjuncts of the hypothesis
    split = ∧-split {⌊ ld-≟ ld ld′ ⌋} {voteRb ms ld v b} eq

  -- THE "I DID THE WORK" DISJUNCT IS MONOTONE: the `kRb` witness survives, and so do the
  -- endpoint test and the body membership inside it.  The `kBody`/`kRelay` witnesses are
  -- absurd — `voteκ` is constantly `false` there.
  ownVote-mono : ∀ {ms ms′} → ms ⊆ ms′ → ∀ ld v
               → ownVote ms ld v ≡ true → ownVote ms′ ld v ≡ true
  ownVote-mono {ms} {ms′} sub ld v eq with any→∈ (voteκ ms ld v) ms eq
  ... | (ld′ , kRb b)    , inn , κeq =
          ∈→any (voteκ ms′ ld v) (sub inn) (voteκ-mono sub ld v ld′ b κeq)
  ... | (_   , kBody _)  , _   , ()
  ... | (_   , kRelay _) , _   , ()

  -- so is the whole vouching test, disjunct by disjunct
  vouched-mono : ∀ {ms ms′} → ms ⊆ ms′ → ∀ w → vouched ms w ≡ true → vouched ms′ w ≡ true
  vouched-mono sub (ld , v) eq with ∨-split eq
  ... | inj₁ l = ∨-inl (memKey-mono sub l)
  ... | inj₂ r = ∨-inr (ownVote-mono sub ld v r)

  -- the gate's monotonicity, as a case on `isPutVote`'s answer alone
  gate-mono-aux : ∀ {ms ms′} → ms ⊆ ms′ → (z : Maybe VoteNeed)
                → maybe′ (vouched ms) true z ≡ true → maybe′ (vouched ms′) true z ≡ true
  gate-mono-aux sub nothing  eq = refl
  gate-mono-aux sub (just w) eq = vouched-mono sub w eq

  -- MINTING ONLY EVER OPENS THE GATE: `vouched` is monotone in the minted list and
  -- every other channel's gate is constantly `true`
  voteGate-mono : ∀ {ms ms′} → ms ⊆ ms′
                → ∀ at a → voteGate ms at a ≡ true → voteGate ms′ at a ≡ true
  voteGate-mono sub at a eq = gate-mono-aux sub (isPutVote at a) eq

  ------------------------------------------------------------------------
  -- The specification S2 names
  ------------------------------------------------------------------------

  -- the generic carrier at the S2 discipline.  `OriginSpecT` is renamed rather than
  -- listed: Agda rejects a name that appears in both `using` and `renaming`.
  open OS.Generic.Origin p t apiES VoteKeyE decVoteKeyE voteMints voteGate voteGate-mono
    using ( Minted; mintedAfter; mintedAfter-⊇; originOffer; OriginSpecAt; specAt-init
          ; OSafe; gateOK; onτ; onEv; noTick; osafe→⊑T )
    renaming (OriginSpecT to VoteSpecT)
    public

  ------------------------------------------------------------------------
  -- The assume-guarantee instance, and the ONE alphabet enumeration
  ------------------------------------------------------------------------

  -- WHAT A LABEL CARRIES: a vote deposit carries the blob it deposits KEYED BY THE
  -- ENDPOINT IT IS DEPOSITED AT; nothing else carries anything.  (This is the `Carries`
  -- of the Wf framework — "needs a justification" — NOT the same thing as `voteMints`.)
  voteCarries : (at : AnyTypes (Net_Api Payload)) → proj₁ at → VoteNeed → Set
  voteCarries at a w = maybe′ (λ z → z ≡ w) ⊥ (isPutVote at a)

  -- WHAT THE MINTED SET MUST SAY ABOUT A CARRIED BLOB-AT-AN-ENDPOINT
  voteWA : Minted → VoteNeed → Set
  voteWA ms w = vouched ms w ≡ true

  -- the state a label leads to: EXACTLY `OriginSafe`'s `mintedAfter` on a visible
  -- label (definitionally — `mintedAfter at a ms = mints at a ++ ms`), and unchanged
  -- on a τ or a `√`.  This equation is what makes the bridge below a five-liner.
  voteNext : Label (⊤ {0ℓ}) → Minted → Minted
  voteNext (ev (evl (evLabel X e a))) ms = voteMints (X , e) a ++ ms
  voteNext _                          ms = ms

  -- the minted set only grows
  voteNext-⊆ : ∀ a ms → ms ⊆ voteNext a ms
  voteNext-⊆ (ev (evl (evLabel X e a))) ms = mintedAfter-⊇ (X , e) a
  voteNext-⊆ (ev (√ _))                 ms = λ q → q
  voteNext-⊆ τ                          ms = λ q → q

  -- EVERY CARRYING CHANNEL IS A `store` CHANNEL.  One clause per `Net_Api` constructor
  -- and, under `store`, one per `StoreTag`, because `isPutVote`'s catch-all does not
  -- reduce until the constructor is known.  This is the whole alphabet tax of S2.
  needs-store : ∀ {X} {e : Net_Api Payload X} {a : X} {w} → voteCarries (X , e) a w
              → Σ[ l ∈ Link ] Σ[ d ∈ Dir ] Σ[ m ∈ StoreTag ]
                  (_≡_ {A = AnyTypes (Net_Api Payload)}
                       (X , e) (StoreCar m , store l d m))
  needs-store {e = store l d stPutVote}       _  = l , d , stPutVote , refl
  needs-store {e = store _ _ stPut}           ()
  needs-store {e = store _ _ stGet}           ()
  needs-store {e = store _ _ (stGetAt _)}     ()
  needs-store {e = store _ _ stPutEB}         ()
  needs-store {e = store _ _ (stGetEBAt _)}   ()
  needs-store {e = store _ _ stPutBody}       ()
  needs-store {e = store _ _ (stGetBody _)}   ()
  needs-store {e = store _ _ stPutTx}         ()
  needs-store {e = store _ _ (stGetTxAt _)}   ()
  needs-store {e = store _ _ (stGetVoteAt _)} ()
  needs-store {e = store _ _ stCert}          ()
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
  -- alphabets and their `Sep`s, and the prototype peer bundle — none of which depends on
  -- WHICH store channel is gated.  RE-EXPORTED, so that `Leios.VoteSystemL` reaches them
  -- through this module instead of re-applying `OriginLeaves.Generic.Leaves` at the same
  -- eleven arguments.
  open OL.Generic.Leaves p t apiES Minted VoteNeed voteCarries voteWA voteNext
                         _⊆_ ⊆-refl ⊆-trans voteNext-⊆ needs-store public

  -- the assume-guarantee carrier at the S2 discipline … also re-exported, so that the
  -- `Wf` a system module folds with is THIS module application's and not a second one
  open BP.Carrier (Net_Api-≟ {Payload}) Minted VoteNeed voteCarries voteWA
                  voteNext _⊆_ ⊆-trans voteNext-⊆
    using ( OK; lbl; Wf; nowW; stepW; wf-mono; wf-mono-G; wf-Skip; wf-deadlock
          ; Sep; _∪α_; wf-Par; wf-⦀; wf-⦀⋆
          -- … and the four only a SYSTEM fold needs
          ; wf-⦀Fin⁺; HideCov; HideKeep; wf-Hide ) public

  -- … and its returning-tree layer, at the SAME arguments, so the two `Wf`s are the
  -- same record
  open BPW.Body (Net_Api-≟ {Payload}) Minted VoteNeed voteCarries voteWA
                voteNext _⊆_ ⊆-refl ⊆-trans voteNext-⊆
    using ( WfR; nowR; stepR; retR; Stable; stable-node; stable-□
          ; wfR-mono; wfR-Ret; wfR-Stop; wfR-Prefix; wfR-Output; wfR-⊓; wfR-□
          ; wfR->>=; wf-loop; wf-loop0; wf-⦀⁺; wf-⦀⁺∈ )

  ------------------------------------------------------------------------
  -- THE BRIDGE
  ------------------------------------------------------------------------

  -- `OK` at a vote deposit IS the gate, and at every other channel the gate is `true`
  gate-ok-aux : (ms : List VoteKeyE) (z : Maybe VoteNeed)
              → (∀ {w} → maybe′ (λ z′ → z′ ≡ w) ⊥ z → vouched ms w ≡ true)
              → maybe′ (vouched ms) true z ≡ true
  gate-ok-aux ms nothing  _ = refl
  gate-ok-aux ms (just w) g = g refl

  -- `OK` at a label IS the gate.  On a vote deposit `Carries` hands the `vouched` fact
  -- over directly; every other channel's gate is `true` by definition of `voteGate`.
  ok→gate : ∀ {X} {e : Net_Api Payload X} {a : X} {ms}
          → (∀ {w} → voteCarries (X , e) a w → voteWA ms w)
          → voteGate ms (X , e) a ≡ true
  ok→gate {X} {e} {a} {ms} f = gate-ok-aux ms (isPutVote (X , e) a) f

  -- A `Wf` FACT ON THE FULL ALPHABET IS AN `OSafe` FACT.  The two carriers agree by
  -- construction: `voteNext` on a visible label IS `mintedAfter`, `OK` at a label IS
  -- the gate (`ok→gate`), and `Wf` on `fullα` guarantees it for every label.  The one
  -- thing `Wf` does not carry is `OSafe`'s `noTick`, which comes from `NoRet` — and
  -- that is exactly right: the obligation belongs to the COMPOSITE, which never
  -- returns, not to the peer bundle, which does.
  wf→osafe : ∀ {ms} {M : Proc} → Wf fullα ms M → NoRet M → OSafe ms M
  wf→osafe {ms = ms} w nr .gateOK {X} {e} {a} st =
    ok→gate {X} {e} {a} {ms} (nowW w ⊆-refl tt st)
  wf→osafe w nr .onτ    st = wf→osafe (stepW w ⊆-refl st tt) (NoRet.stepNR nr st)
  wf→osafe w nr .onEv   st =
    wf→osafe (stepW w ⊆-refl st (nowW w ⊆-refl tt st)) (NoRet.stepNR nr st)
  wf→osafe w nr .noTick st = noRet→noTick nr st

  ------------------------------------------------------------------------
  -- The fourteen threads that need no key
  --
  -- Each is a `loop`/`loop0` over a chain of prefixes and outputs on channels other
  -- than `store … stPutVote`, so `noNeed` holds at every offer by reduction and the
  -- whole discharge is `OffersOnly-Prefix`/`-Output`/`->>=` plumbing.
  ------------------------------------------------------------------------

  -- THE FORGE THREAD: `env … envForge`, then at most an EB-body deposit, then — for a
  -- certificate-carrying block whose announcement the guard accepts — the `stHasCert`
  -- rendezvous and the RB deposit.  None of the four carries a vote blob.
  oo-forgeL : ∀ n → OffersOnly noNeed (forgeL n)
  oo-forgeL n = OffersOnly-loop0 (OffersOnly-Prefix (λ _ → λ ()) body)
    where
    -- the certificate half of one pass: a rendezvous and an RB deposit
    cert : ∀ b → OffersOnly noNeed (forgeCertL n b)
    cert b with rbCert b
    ... | nothing = OffersOnly-Skip
    ... | just r  = OffersOnly-Prefix₀ (λ _ → λ ())
                      (OffersOnly-Output (λ ()) OffersOnly-Skip)

    -- one pass, under the forge guard and the optional EB
    body : ∀ mb → OffersOnly noNeed (forgeBodyL n mb)
    body (me , b) with forgeOK (me , b)
    ... | false = OffersOnly-Skip
    ... | true with me
    ...   | nothing = cert b
    ...   | just eb = OffersOnly-Output (λ ()) (cert b)

  -- the EB index: read the k-th held RB, record its announced EB entry
  oo-ebIndex : ∀ n → OffersOnly noNeed (ebIndex n)
  oo-ebIndex n = OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → λ ()) (body k))
    where
    -- the entry deposit, when the RB announces an EB
    body : ∀ k b → OffersOnly noNeed
             (maybe′ (λ h → putEBEv n ! (h , slotOf b) ⟶ Ret (suc k))
                     (Ret (suc k)) (announcedEB b))
    body k b with announcedEB b
    ... | nothing = OffersOnly-Ret
    ... | just h  = OffersOnly-Output (λ ()) OffersOnly-Ret

  -- the submission thread: environment transaction, then mempool deposit
  oo-submit : ∀ n → OffersOnly noNeed (submit n)
  oo-submit n =
    OffersOnly-loop0 (OffersOnly-Prefix (λ _ → λ ())
                        (λ _ → OffersOnly-Output (λ ()) OffersOnly-Skip))

  -- the certificate sink: one `stCert`, absorbed
  oo-certSink : ∀ n → OffersOnly noNeed (certSink n)
  oo-certSink n = OffersOnly-loop0 (OffersOnly-Prefix (λ _ → λ ()) (λ _ → OffersOnly-Skip))

  -- the Praos client thread: ChainSync/BlockFetch and the RB store's `stPut`
  oo-clientLoop : ∀ n ld → OffersOnly noNeed (clientLoop n ld)
  oo-clientLoop n (l , d) =
    OffersOnly-loop0 (OffersOnly-Prefix₀ (λ _ → λ ()) (OffersOnly-Prefix (λ _ → λ ()) k))
    where
    -- the RollForward continuation: request the range, receive the block, store it
    k : ∀ a → OffersOnly noNeed (clientBody-k n l d a)
    k (header b , _) =
      OffersOnly-Output (λ ())
        (OffersOnly-Prefix (λ _ → λ ()) (λ _ → OffersOnly-Output (λ ()) OffersOnly-Skip))

  -- the tail of a Praos server round, on the block the store handed over
  oo-serverBody-k : ∀ n l d b → OffersOnly noNeed (serverBody-k n l d b)
  oo-serverBody-k n l d b =
    OffersOnly-Prefix₀ (λ _ → λ ())
      (OffersOnly-Output (λ ())
        (OffersOnly-Prefix (λ _ → λ ()) (λ _ →
          OffersOnly-Prefix₀ (λ _ → λ ())
            (OffersOnly-Output (λ ())
              (OffersOnly-Prefix₀ (λ _ → λ ()) OffersOnly-Skip)))))

  -- the read-pointer Praos server thread
  oo-serverLoopL : ∀ n ld → OffersOnly noNeed (serverLoopL n ld)
  oo-serverLoopL n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix₀ (λ _ → λ ())
      (OffersOnly-Prefix (λ _ → λ ()) (λ b →
        OffersOnly->>= (oo-serverBody-k n l (opposite d) b) (λ _ → OffersOnly-Ret))))

  -- the LeiosNotify announce thread, on the prototype's `lnpSendBlockAnnouncement`
  oo-lnServerLoopL : ∀ n ld → OffersOnly noNeed (lnServerLoopL n ld)
  oo-lnServerLoopL n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → λ ())
                             (λ b → OffersOnly-Output (λ ()) OffersOnly-Ret))

  -- the tx-closure gate: mempool READS only (`stGetTx`), so it keeps any `noNeed` continuation
  oo-awaitTxs : ∀ n (hs : List (TxHash × Size)) {P}
              → OffersOnly noNeed P → OffersOnly noNeed (awaitTxs n hs P)
  oo-awaitTxs n []             oo = oo
  oo-awaitTxs n ((h , _) ∷ hs) oo = OffersOnly-Prefix (λ _ → λ ()) (λ _ → oo-awaitTxs n hs oo)

  -- the body-offer thread: it READS a body (`stGetBody`, which mints) and offers the
  -- point, its size and the tx-closure offer — depositing nothing
  oo-bodyOfferLoop : ∀ n ld → OffersOnly noNeed (bodyOfferLoop n ld)
  oo-bodyOfferLoop n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → λ ()) (body k))
    where
    -- the two offers, when the RB announces an EB whose body the node holds
    body : ∀ k b → OffersOnly noNeed
             (maybe′ (λ h → getBodyEv n h ⟶ (λ eb →
                        Output ⦃ DecEq-Offer ⦄ (apiLP l (opposite d) lnpSendBlockOffer)
                          ((h , slotOf b) , ebSize eb)
                          (awaitTxs n (ebTxs h)
                            (Output ⦃ DecEq-EBPoint ⦄
                               (apiLP l (opposite d) lnpSendBlockTxsOffer)
                               (h , slotOf b) (Ret (suc k))))))
                     (Ret (suc k)) (announcedEB b))
    body k b with announcedEB b
    ... | nothing = OffersOnly-Ret
    ... | just h  = OffersOnly-Prefix (λ _ → λ ()) (λ eb →
                      OffersOnly-Output ⦃ DecEq-Offer ⦄ (λ ())
                        (oo-awaitTxs n (ebTxs h)
                          (OffersOnly-Output ⦃ DecEq-EBPoint ⦄ (λ ()) OffersOnly-Ret)))

  -- the vote-offer thread: it reads a blob and sends it on
  oo-voteOfferLoop : ∀ n ld → OffersOnly noNeed (voteOfferLoop n ld)
  oo-voteOfferLoop n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → λ ())
                             (λ v → OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ (λ ())
                                      OffersOnly-Ret))

  -- the EB-serve thread: the reported request, the body read, the body on the wire
  oo-ebServeLoop : ∀ n ld → OffersOnly noNeed (ebServeLoop n ld)
  oo-ebServeLoop n (l , d) =
    OffersOnly-loop0 (OffersOnly-Prefix (λ _ → λ ()) (λ q →
      OffersOnly-Prefix (λ _ → λ ()) (λ eb → OffersOnly-Output (λ ()) OffersOnly-Skip)))

  -- the reply builder of the tx-closure server: a mempool read per served offset, then
  -- one offset-indexed reply
  oo-serveTxs : ∀ n l d q bm acc → OffersOnly noNeed (serveTxs n l d q bm acc)
  oo-serveTxs n l d q []       acc =
    OffersOnly-Output ⦃ DecEq-TxsReply ⦄ (λ ()) OffersOnly-Skip
  oo-serveTxs n l d q (o ∷ os) acc with at? o (ebTxs (proj₁ q))
  ... | nothing      = oo-serveTxs n l d q os acc
  ... | just (h , _) = OffersOnly-Prefix (λ _ → λ ())
                         (λ tx′ → oo-serveTxs n l d q os (acc ++ ((o , tx′) ∷ [])))

  -- the tx-closure serve thread
  oo-ebTxsServeLoop : ∀ n ld → OffersOnly noNeed (ebTxsServeLoop n ld)
  oo-ebTxsServeLoop n (l , d) =
    OffersOnly-loop0 (OffersOnly-Prefix (λ _ → λ ()) (λ { (q , bm) →
      OffersOnly-Prefix (λ _ → λ ()) (λ _ → oo-serveTxs n l (opposite d) q bm []) }))

  -- every REQUESTED transaction pulled off the wire, deposited in the mempool; the
  -- membership guard only drops deposits, so both arms are `noNeed`
  oo-putAllTx : ∀ n ids txs → OffersOnly noNeed (putAllTx n ids txs)
  oo-putAllTx n ids []         = OffersOnly-Skip
  oo-putAllTx n ids (t′ ∷ txs) with memberOfNL (txHash t′) ids
  ... | true  = OffersOnly-Output (λ ()) (oo-putAllTx n ids txs)
  ... | false = oo-putAllTx n ids txs

  -- the TxSubmission pull thread
  oo-tsPull : ∀ n ld → OffersOnly noNeed (tsPull n ld)
  oo-tsPull n (l , d) =
    OffersOnly-loop0 (OffersOnly-Output ⦃ DecEq-ℕ×ℕ ⦄ (λ ())
      (OffersOnly-Prefix (λ _ → λ ()) (λ ids →
        OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ (λ ())
          (OffersOnly-Prefix (λ _ → λ ()) (λ txs → oo-putAllTx n ids txs)))))

  -- the TxSubmission serve thread: an id out of the mempool, then the transaction
  -- itself — never manufactured from its hash
  oo-tsServe : ∀ n ld → OffersOnly noNeed (tsServe n ld)
  oo-tsServe n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → λ ()) (λ _ →
      OffersOnly-Prefix (λ _ → λ ()) (λ tx′ →
        OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ (λ ())
          (OffersOnly-Prefix (λ _ → λ ()) (λ _ →
            OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ (λ ()) OffersOnly-Ret)))))

  -- the guarded body deposit of a fetch: needs no key either way
  oo-fetchDep : ∀ n′ h′ eb
              → OffersOnly noNeed
                  ((putBodyEv n′ ! eb ⟶ Skip {0ℓ}) ◁ ⌊ ebHash eb ≟ h′ ⌋ ▷ Skip {0ℓ})
  oo-fetchDep n′ h′ eb with ⌊ ebHash eb ≟ h′ ⌋
  ... | true  = OffersOnly-Output (λ ()) OffersOnly-Skip
  ... | false = OffersOnly-Skip

  -- the reaction to a body offer: request the offered point, receive the body, deposit
  -- it if it hashes to what was asked for
  oo-fetchBody : ∀ n′ l d qs → OffersOnly noNeed (fetchBody n′ l d qs)
  oo-fetchBody n′ l d (q , _) =
    OffersOnly-Output ⦃ DecEq-EBPoint ⦄ (λ ())
      (OffersOnly-Prefix (λ _ → λ ()) (oo-fetchDep n′ (proj₁ q)))

  -- every checked entry of a tx-closure reply, deposited in the MEMPOOL
  oo-putChecked : ∀ n′ h es → OffersOnly noNeed (putChecked n′ h es)
  oo-putChecked n′ h []              = OffersOnly-Skip
  oo-putChecked n′ h ((o , tx′) ∷ es) with at? o (ebTxs h)
  ... | nothing      = oo-putChecked n′ h es
  ... | just (k , _) with ⌊ txHash tx′ ≟ k ⌋
  ...   | true  = OffersOnly-Output (λ ()) (oo-putChecked n′ h es)
  ...   | false = oo-putChecked n′ h es

  -- the reaction to a tx-closure offer: block at the body, request every offset, and
  -- deposit the checked entries.  TRANSACTIONS, not blobs.
  oo-fetchTxs : ∀ n′ l d q → OffersOnly noNeed (fetchTxs n′ l d q)
  oo-fetchTxs n′ l d q =
    OffersOnly-Prefix (λ _ → λ ()) (λ _ →
      OffersOnly-Output ⦃ DecEq-TxsRequest ⦄ (λ ())
        (OffersOnly-Prefix (λ _ → λ ()) (λ { (q′ , es) → guard q′ es })))
    where
    -- the echoed-point check around the deposit
    guard : ∀ q′ es → OffersOnly noNeed
              (putChecked n′ (proj₁ q) es ◁ ⌊ DecEq-EBPoint ._≟_ q′ q ⌋ ▷ Skip {0ℓ})
    guard q′ es with ⌊ DecEq-EBPoint ._≟_ q′ q ⌋
    ... | true  = oo-putChecked n′ (proj₁ q) es
    ... | false = OffersOnly-Skip

  ------------------------------------------------------------------------
  -- THE TWO CONTENT-BEARING LEAVES
  --
  -- The only two threads that ever deposit a vote.  Each reaches its deposit
  -- through a chain of prefixes whose EARLIER steps minted the very keys the
  -- deposit needs — a gate that opens in the middle of a loop body, which is
  -- exactly what a state-independent alphabet cannot express and what
  -- `WfR`'s `wfR-Prefix`/`wfR-Output`/`wf-loop` are for.
  ------------------------------------------------------------------------

  -- THE VOTER.  `voterBody` reads the k-th oldest HELD RB — which MINTS `kRb b` — then
  -- BLOCKS at `stGetBody h` for the body of the EB that RB announces, which MINTS
  -- `kBody h`, and only then deposits `mkVoteBlob (voterOf n) (rbHash b)`.  Both
  -- conjuncts of `voteκ` are discharged by those two mints, and `blobRb-mk` is spent
  -- here and nowhere else in the campaign.
  wf-voter : ∀ {ms} n → Wf fullα ms (voter n)
  wf-voter n = wf-loop (λ _ _ _ → tt) (λ _ k _ → vbody k) tt
    where
    -- the gate at the deposit: the RB read two steps earlier is the `kRb` witness, and
    -- the body read one step earlier is the `kBody` fact inside it
    gate-here : ∀ {s} (b : Block) (h : EBHash) → announcedEB b ≡ just h
              → (homeOf n , kRb b) ∈ s → (homeOf n , kBody h) ∈ s
              → OK s (lbl (putVoteEv n) (mkVoteBlob (voterOf n) (rbHash b)))
    gate-here {s} b h eqb mrb mbd refl =
      ∨-inr (∈→any (voteκ s (homeOf n) (mkVoteBlob (voterOf n) (rbHash b))) mrb
                   (∧-join {⌊ ld-≟ (homeOf n) (homeOf n) ⌋}
                           {voteRb s (homeOf n) (mkVoteBlob (voterOf n) (rbHash b)) b}
                           (⌊ld⌋-refl (homeOf n)) (∧-join hEq bEq)))
      where
      -- the blob names exactly the ranking block the node read
      hEq : ⌊ rbHash b ≟ blobRb (mkVoteBlob (voterOf n) (rbHash b)) ⌋ ≡ true
      hEq rewrite blobRb-mk (voterOf n) (rbHash b) = ⌊≟⌋-refl (rbHash b)

      -- … and the body that ranking block announces was read too, at the same endpoint
      bEq : maybe′ (λ h′ → memKey (homeOf n , kBody h′) s) false (announcedEB b) ≡ true
      bEq rewrite eqb = ∈→memKey _ _ mbd

    -- the tail of one pass, once the ranking block is in hand.  `mem` is the mint the
    -- FIRST step made: `wfR-Prefix`'s continuation is universally quantified over every
    -- larger state, so the fact has to travel as a premise, not as an equation.
    vtail : ∀ {s} k (b : Block) → (homeOf n , kRb b) ∈ s → WfR fullα s (λ _ _ → ⊤)
              (maybe′ (λ h → getBodyEv n h ⟶ (λ _ →
                         putVoteEv n ! mkVoteBlob (voterOf n) (rbHash b) ⟶ Ret (suc k)))
                      (Ret (suc k)) (announcedEB b))
    vtail k b mem with announcedEB b in eqb
    ... | nothing = wfR-Ret (λ _ → tt)
    ... | just h  = wfR-Prefix (λ _ _ _ → λ ()) (λ le₂ eb _ →
                      wfR-Output (λ le₃ _ → gate-here b h eqb
                                              (le₃ (there (le₂ mem))) (le₃ (here refl)))
                                 (λ _ _ → wfR-Ret (λ _ → tt)))

    -- one pass of the voting thread
    vbody : ∀ {s} k → WfR fullα s (λ _ _ → ⊤) (voterBody n k)
    vbody k = wfR-Prefix (λ _ _ _ → λ ()) (λ _ b _ → vtail k b (here refl))

  -- EVERY DELIVERED BLOB IS DEPOSITED, and the delivery that carried them minted one
  -- RELAY key per blob AT THE DEPOSITING NODE'S OWN ENDPOINT — so each deposit's gate
  -- opens on its left disjunct, by induction on the delivered list.  This is why S2 is
  -- TRUE of a node that relays.  The hypothesis is keyed by `homeOf n′`, which is exactly
  -- where `putVoteEv n′` fires.
  wf-putAllVotes : ∀ {s} n′ vs
                 → (∀ {v} → v ∈ vs → memKey (homeOf n′ , kRelay v) s ≡ true)
                 → WfR fullα s (λ _ _ → ⊤) (putAllVotes n′ vs)
  wf-putAllVotes n′ []       h = wfR-Ret (λ _ → tt)
  wf-putAllVotes n′ (v ∷ vs) h =
    wfR-Output (λ le _ → λ { refl → ∨-inl (memKey-mono le (h (here refl))) })
               (λ le _ → wf-putAllVotes n′ vs (λ q → memKey-mono le (h (there q))))

  -- THE NOTIFY CLIENT.  Four branches after the long-poll request: an announcement
  -- (nothing), a body offer (fetches and deposits a BODY), a tx-closure offer (deposits
  -- TRANSACTIONS) and a votes reply — the only one with content.
  -- IT TAKES THE ENDPOINT'S MEMBERSHIP: the delivery mints at `homeAt (l , d)` and the
  -- deposits it licenses are at `homeOf n`, so the leaf has to know that `(l , d)` really
  -- is one of `n`'s endpoints.
  wf-lnClient : ∀ {ms} n ld → ld ∈ endpointsList n → Wf fullα ms (lnClientLoopL n ld)
  wf-lnClient n (l , d) mem = wf-loop0 (wfR-Prefix (λ _ _ _ → λ ()) (λ _ _ _ → choice))
    where
    -- the announcement branch
    annB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
             (apiLP l d lnpRecvBlockAnnouncement ⟶ (λ _ → Skip))
    annB = wfR-free (OffersOnly-Prefix (λ _ → λ ()) (λ _ → OffersOnly-Skip)) tt

    -- the body-offer branch
    offB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
             (apiLP l d lnpRecvBlockOffer ⟶ fetchBody n l d)
    offB = wfR-free (OffersOnly-Prefix (λ _ → λ ()) (oo-fetchBody n l d)) tt

    -- the tx-closure branch
    txB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
            (apiLP l d lnpRecvBlockTxsOffer ⟶ fetchTxs n l d)
    txB = wfR-free (OffersOnly-Prefix (λ _ → λ ()) (oo-fetchTxs n l d)) tt

    -- A DELIVERY AT THIS ENDPOINT MINTS AT THIS NODE'S OWN DEPOSIT ENDPOINT, because
    -- `endAt l d` IS `n` — `Topology.endpoints-sound`, through `sound-at`.  THIS is the
    -- one leaf the threaded membership is spent at.
    minted-here : ∀ (vs : List VoteBlob) {v} → v ∈ vs
                → (homeOf n , kRelay v) ∈ map (λ w → (homeAt (l , d) , kRelay w)) vs
    minted-here vs {v} q =
      subst (λ z → (z , kRelay v) ∈ map (λ w → (homeAt (l , d) , kRelay w)) vs)
            (cong homeOf (sound-at n l d mem))
            (∈-map⁺ (λ w → (homeAt (l , d) , kRelay w)) q)

    -- the votes branch: deposit exactly the blobs the reply carried, whose relay keys
    -- that very reply minted at this node's deposit endpoint
    votB : ∀ {s} → WfR fullα s (λ _ _ → ⊤) (apiLP l d lnpRecvVotes ⟶ putAllVotes n)
    votB = wfR-Prefix (λ _ _ _ → λ ()) (λ _ vs _ →
             wf-putAllVotes n vs (λ q → ∈→memKey _ _ (∈-++⁺ˡ (minted-here vs q))))

    -- the four branches, offered together
    choice : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
               ((apiLP l d lnpRecvBlockAnnouncement ⟶ (λ _ → Skip))
               □ ((apiLP l d lnpRecvBlockOffer    ⟶ fetchBody n l d)
               □ ((apiLP l d lnpRecvBlockTxsOffer ⟶ fetchTxs  n l d)
               □  (apiLP l d lnpRecvVotes         ⟶ putAllVotes n))))
    choice =
      wfR-□ _ _ (stable-node refl)
                (stable-□ (stable-node refl)
                          (stable-□ (stable-node refl) (stable-node refl)))
                annB
                (wfR-□ _ _ (stable-node refl)
                           (stable-□ (stable-node refl) (stable-node refl))
                           offB
                           (wfR-□ _ _ (stable-node refl) (stable-node refl) txB votB))

  ------------------------------------------------------------------------
  -- The assembly
  ------------------------------------------------------------------------

  -- one endpoint's ten threads.  Nine of them carry nothing and ignore the membership;
  -- only the Notify client spends it.
  wf-endpoint : ∀ {ms} n e → e ∈ endpointsList n → Wf fullα ms (endpointThreadsL n e)
  wf-endpoint n e mem =
    wf-⦀ (wf-free (oo-clientLoop n e))
      (wf-⦀ (wf-free (oo-serverLoopL n e))
      (wf-⦀ (wf-lnClient n e mem)
      (wf-⦀ (wf-free (oo-lnServerLoopL n e))
      (wf-⦀ (wf-free (oo-bodyOfferLoop n e))
      (wf-⦀ (wf-free (oo-voteOfferLoop n e))
      (wf-⦀ (wf-free (oo-ebServeLoop n e))
      (wf-⦀ (wf-free (oo-ebTxsServeLoop n e))
      (wf-⦀ (wf-free (oo-tsPull n e)) (wf-free (oo-tsServe n e))))))))))

  -- every incident endpoint's threads, each handed its own membership in
  -- `endpointsList n` — which is definitionally the head-plus-tail list this fold runs
  -- over, so `wf-⦀⁺∈` supplies it with nothing to prove
  wf-allThreads : ∀ {ms} n → Wf fullα ms (allThreadsL n)
  wf-allThreads n =
    wf-⦀⁺∈ (endpointThreadsL n) (proj₁ (endpointsOf n)) (proj₂ (endpointsOf n))
           (λ e mem → wf-endpoint n e mem)

  -- the five node-level threads and every endpoint's ten
  wf-threads : ∀ {ms} n
             → Wf fullα ms (forgeL n ⦀ (ebIndex n ⦀ (voter n ⦀
                              (submit n ⦀ (certSink n ⦀ allThreadsL n)))))
  wf-threads n =
    wf-⦀ (wf-free (oo-forgeL n))
      (wf-⦀ (wf-free (oo-ebIndex n))
      (wf-⦀ (wf-voter n)
      (wf-⦀ (wf-free (oo-submit n))
      (wf-⦀ (wf-free (oo-certSink n)) (wf-allThreads n)))))

  -- A GATE-CARRYING THREAD GROUP AGAINST ANY STORE GROUP.  The threads carry the gate,
  -- the stores guarantee nothing, and the one key-needing channel is inside `storeES`,
  -- so `Sep` asks the stores for nothing.  Stated for an ARBITRARY thread and store
  -- operand so that `VoteSoundBad`'s reduced composite is assembled by the same lemma.
  wf-withStores : ∀ {ms} {th st : Proc} → Wf fullα ms th → Wf fullα ms (th ∥⇘ storeES ⇙ st)
  wf-withStores w = wf-mono-G (λ _ _ _ → inj₁ tt) (wf-Par storeES sep-store w wf-∅)

  -- THE NODE LOGIC, at the shipped thread group
  wf-logic : ∀ {ms} n → Wf fullα ms (nodeLogicL n st₀)
  wf-logic n = wf-withStores (wf-threads n)

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

  -- S2 — VOTE SOUNDNESS, node-local.  A node running `nodeLogicL` from empty stores
  -- deposits no vote blob it cannot vouch for: either a neighbour delivered that exact
  -- blob on `lnpRecvVotes`, or the node itself read the ranking block the blob names
  -- AND the body of the EB that block announces — all of it AT ONE OF THAT NODE'S OWN
  -- ENDPOINTS.  No validity is asserted: the prototype's votes carry no verdict at all.
  -- LEVEL: node — `Leios.VoteSystemL` lifts this to the whole network.
  VoteSound : Set₁
  VoteSound = ∀ (n : Node) → VoteSpecT ⊑T nodeP n (nodeLogicL n st₀)

  -- S2 FOR ANY NODE LOGIC THAT CARRIES THE GATE AND NEVER RETURNS.  The bundle and the
  -- logic compose on `apiES` at the full guarantee alphabet (`Sep apiES` is trivial
  -- there), and `wf→osafe` then `osafe→⊑T` turn that one `Wf` fact into the trace
  -- refinement.  The logic is a PARAMETER so that `VoteSoundBad`'s controlled
  -- comparison runs through exactly this assembly.
  soundOf : ∀ n (lg : Proc) → Wf fullα [] lg → NoRet lg → VoteSpecT ⊑T nodeP n lg
  soundOf n lg w nr =
    osafe→⊑T (wf→osafe (wf-mono-G (λ _ _ _ → inj₁ tt)
                         (wf-Par apiES sep-api (wf-linkBundlesP n) w))
                       (NoRet-ParR apiES nr))

  -- S2, PROVED, at the shipped node logic from empty stores
  voteSound : VoteSound
  voteSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)

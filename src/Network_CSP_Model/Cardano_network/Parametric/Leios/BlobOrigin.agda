{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S2′, BLOB ORIGIN: a node never invents a vote
-- blob in somebody else's name.
--
-- WHAT S2′ SAYS.  S2 (`VoteSound`) asks what BACKS a vote deposit: either a
-- neighbour delivered the blob, or the node did the reading work itself.  It
-- says nothing about WHOSE ballot the blob claims to be, and a relayed blob's
-- own origin is explicitly left open there.  S2′ is that missing half.  A
-- node deposits a vote blob `v` in its vote store (`store home(n) stPutVote
-- ! v`) only if
--
--   * `v` is attributed to the node's OWN voter — the deposit happens at the
--     home endpoint of the node that `blobVoter v` names — in which case the
--     node is casting its own ballot and owes nothing; or
--   * `apiLP l d lnpRecvVotes ! vs` delivered `v` — the node is RELAYING,
--     and a relayed blob has an origin somewhere on the wire.
--
-- THE STATEMENT, IN THE WORDS THAT MAY BE QUOTED.  S2′ rules out *node `n`
-- depositing a vote blob attributed to ANOTHER node's voter unless an
-- `lnpRecvVotes` delivery at `n` carried that exact blob; it does NOT show
-- the claimed voter really cast it, and it leaves blobs the node attributes
-- to ITSELF entirely free, including fabricated or self-relabelled ones.*
--
-- WHAT S2′ THEREFORE DOES **NOT** RULE OUT — four things, all deliberate:
--
--   1. a blob the node FABRICATES in its OWN name (S2 `VoteSound` is what
--      asks whether the node did the reading work behind such a ballot);
--   2. a blob it received and RELABELLED INTO ITS OWN NAME — likewise S2's
--      business, not S2′'s, because the gate's first disjunct licenses it;
--   3. any claim that the voter named on a RELAYED blob really cast it:
--      "delivered" here means only "an `lnpRecvVotes` event happened", never
--      "voter `u` signed it".  The wire is unconstrained at node level;
--   4. a blob claiming a voter id that NO node owns.  `nodeOf` is pinned by
--      `nodeOf-voterOf` only on the IMAGE of `voterOf`; if `VoterId` is
--      strictly larger than that image, a blob naming an unowned id that
--      `nodeOf` happens to send to `n` passes the first disjunct freely.
--      (Empty at `LeiosInstanceL`, where `VoterId = Node` and `nodeOf = id`,
--      but a system lift must know.)
--
-- THE CARRYING RELATION IS ENDPOINT-INDEXED, DELIBERATELY.  An
-- endpoint-blind obligation ("every deposit names a delivered blob") is
-- STRICTLY STRONGER, is not S2′, and is FALSE of `NodeLogicL`: the `voter`
-- thread casts ballots that no wire ever carried.  The asymmetry between
-- casting and relaying is the whole content of this theorem, so it is built
-- into `blobCarries`, which is `⊥` at the claimed voter's own endpoint.
--
-- "ITS OWN VOTER" IS A NODE-LEVEL READING — READ THIS BEFORE ANY SYSTEM
-- LIFT.  Like S2's and S3's, this discipline is ENDPOINT-AGNOSTIC in its
-- MINTS: `blobMints` mints on `apiLP _ _ lnpRecvVotes` for EVERY link and
-- direction, so nothing in the minted set says WHICH endpoint received the
-- delivery.  (The GATE is endpoint-sensitive — `atVoter` compares the
-- deposit's endpoint against the claimed voter's home — but that only
-- decides whether an obligation arises, not who discharged it.)  CONSEQUENCE:
-- with more than one node in the same composite, a `lnpRecvVotes` delivered
-- at node X would licence a relay deposit at node Y.  A system-level S2′
-- must first make the key ENDPOINT-INDEXED, exactly as `VoteSound`'s header
-- prescribes for S2 — mint `(l , d , v)` and gate a `stPutVote` at `(l , d)`
-- on keys carrying that same `(l , d)`.  Until that is done, no result here
-- may be quoted above node level.  At node level the reading is licensed for
-- the reason S2's header records: inside `nodeP n (nodeLogicL n st₀)` the
-- only `store` channels that occur are the `homeOf n` ones, and no peer of
-- the bundle offers a `store` channel at all.
--
-- THE KEY IS THE BLOB ITSELF (`Minted = List VoteBlob`): S2′ asks only
-- whether THIS blob was delivered, so there is nothing to sort.
--
-- HOW IT IS PROVED.  The same assume-guarantee route S2 takes —
-- `BlockProvenance.Carrier` plus `BlockProvenanceWfR.Body`, the shared
-- leaves of `OriginLeaves`, and `wf→osafe` back into `OriginSafe`.  THE
-- GATED CHANNEL IS EMITTED BY A THREAD (the `voter` and the Notify client
-- both drive `putVoteEv`), never by a store, so this is S2's ORIENTATION and
-- not S3's: the thread group carries `fullα`, the store group `∅α`, the `Sep`
-- is `sep-store`, and the assembly is `wf-withStores`.
--
-- THE VACUOUS THREAD LEAVES ARE NOT RE-WRITTEN.  S2′'s carrying relation is
-- S2's plus a side condition (`atVoter … ≡ false`), so
-- `blobCarries → voteCarries` pointwise (`carries-VS`), and every thread
-- that carries nothing for S2 carries nothing here — `OffersOnly-mono`
-- transports each in one line (`wf-vs`).  `VoteSound` defines 21 `oo-*`
-- facts and this module names SIXTEEN of them; the other five
-- (`oo-fetchDep`, `oo-putAllTx`, `oo-putChecked`, `oo-serverBody-k`,
-- `oo-serveTxs`) are helpers consumed inside those sixteen.  That is why
-- this module imports `VoteSound`: for those leaves and its four Boolean
-- lemmas, NOT for any part of S2's statement.  Only the two content-bearing
-- leaves, `wf-voter` and `wf-lnClient`, are proper to S2′ — and they are
-- where the two disciplines genuinely differ.
--
-- NON-VACUITY IS PROVED HERE, GENERICALLY, not only exhibited at an
-- instance by the control: `homeOf-inj` (off `Topology.endpoints-sound`)
-- and `atVoter-bites` say that for EVERY topology and EVERY node, a blob
-- claiming a voter that belongs to a different node has `atVoter ≡ false`
-- at the node's own deposit endpoint — so the obligation really arises and
-- only a delivery can discharge it.  `voterOf-inj` records that `voterOf`'s
-- injectivity is DERIVABLE from `nodeOf-voterOf` (a left inverse forces
-- it), so no system lift need buy that premise separately.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.BlobOrigin where

open import Level using (Level; 0ℓ)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (_≟_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Class.DecEq using (DecEq)
import Class.DecEq.Instances as DecEqI
-- `Link = Fin numLinks`, so the endpoint equality below needs the `Fin` instance in
-- instance scope (`LiveChanCS.agda:115` is the precedent for importing it by name)
open import Class.DecEq.Instances using (DecEq-Fin)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Topology using (Topology; opposite)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
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
-- S2, for its twenty-one vacuous thread leaves and the shared Boolean lemmas.  NOTHING
-- of S2's STATEMENT is used here; see the module header.
import Cardano_network.Parametric.Leios.VoteSound as VS
open import Cardano_network.Parametric.Leios.VoteSound
  using (∨-split; ∨-inl; ∨-inr; ⌊≟⌋-refl)

-- the S2′ origin discipline, parametric in the network parameters, the Leios
-- parameters, the topology, the api alphabet, the node-to-voter map — the five
-- `NodeLogicL.Generic` takes — and the INVERSE of that map, which is what lets the
-- gate ask "is this deposit at the claimed voter's own endpoint?"
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p)
  -- which node casts a given voter's ballots.  Instances take `VoterId := Node`,
  -- `voterOf := id`, `nodeOf := id`.
  (nodeOf : Params.VoterId p → Topology.Node t)
  -- … and the round-trip law that makes the two a retraction on nodes
  (nodeOf-voterOf : ∀ n → nodeOf (voterOf n) ≡ n) where

  open Params p
    using ( Block; VoterId; VoteBlob; EB; EBHash; linkConfig
          ; rbHash; announcedEB; decVoteBlob )
  open LeiosP p using (LeiosEb)
  open LeiosP.LeiosParams lp using (mkVoteBlob; blobVoter; blobVoter-mk)
  -- EVERY tag named below MUST appear here: an unlisted tag silently becomes a pattern
  -- VARIABLE and the carrier table turns into a stuck term (campaign ledger, gotcha 1).
  open N p
    using ( Link; Net_Api; Net_Api-≟; StoreTag; StoreCar
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; apiLP; store; env; break
          ; stPut; stGet; stGetAt; stPutEB; stGetEBAt; stPutBody; stGetBody
          ; stPutTx; stGetTxAt; stGetTx; stPutVote; stGetVoteAt; stCert; stHasCert
          ; lnpRecvBlockAnnouncement; lnpRecvBlockOffer; lnpRecvBlockTxsOffer
          ; lnpRecvVotes )
  open D p using (Payload)
  -- (wholesale, as `NetworkPar` and `OriginLeaves`: `Dir`, its decidable equality and
  -- the six `IDs` constructors)
  open import Cardano_network.Base
  open Topology t using (Node; endpointsOf; endpointsList; endpoints-sound)
  -- `endAt` is NOT opened: the record's derived `endAt` is a pattern-matching lambda, and
  -- the opened copy does not unify with the one inside `endpoints-sound`'s instantiated
  -- type (measured `UnequalTerms`).  The qualified projection is the term that does.
  endAtT : Link → Dir → Node
  endAtT = Topology.endAt t
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (EventSet; Skip; Ret; _⦀_; _∥⇘_⇙_; Prefix; Output; _□_)
  open import Cardano_network.Parametric.Node p t apiES
    using (Proc; nodeWith; bundleAtWith; linkBundlesWith)
  open import Semantics.LTS
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; √; evLabel)
  open import Semantics.Failures
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⊑T_)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using ( OffersOnly; OffersOnly-mono; NoRet
          ; OffersOnly-Prefix; OffersOnly-Skip
          ; NoRet-Par; NoRet-⦀; NoRet-loop0 )
  -- the right-sided `NoRet`: a node puts its TERMINATING peer bundle on the LEFT of
  -- `∥⇘ apiES ⇙`, and `DRCongruenceRep.NoRet-Par` reads the left operand
  open BPS.Generic p t apiES using (NoRet-ParR)
  open NL.Generic p t apiES using (storeES; homeOf)
  open NLL.Generic p lp t apiES voterOf
    using ( nodeLogicL; st₀; DecEq-⊤poly
          ; getBodyEv; putVoteEv
          ; forgeL; forgeCert; ebIndex; voter; voterBody; submit; certSink
          ; lnClientLoopL; fetchBody; fetchTxs; putAllVotes
          ; endpointThreadsL; allThreadsL )
  open OS using (memberOf; memberOf-mono; ∈→memberOf)
  open OS.Generic p t apiES using (noRet→noTick)
  -- the PROTOTYPE peer bundle, whose nine `Wf` facts live in `OriginLeaves.Leaves`
  open import Cardano_network.Parametric.Leios.PeersP p using (nodeBundleP)
  -- S2's `Generic`, at the SAME five parameters, for its vacuous thread leaves
  module VSG = VS.Generic p lp t apiES voterOf

  ------------------------------------------------------------------------
  -- The origin discipline
  ------------------------------------------------------------------------

  instance
    -- the endpoint equality `atVoter` compares on.  `Link × Dir` has no ambient product
    -- instance here (`Class.DecEq.Instances` is imported QUALIFIED), so this is the one
    -- `DecEq (Link × Dir)` in scope and `⌊≟⌋-refl` below resolves to it.
    DecEq-Endpoint : DecEq (Link × Dir)
    DecEq-Endpoint = DecEqI.DecEq-×

  -- IS THIS ENDPOINT THE HOME ENDPOINT OF THE NODE THE BLOB CLAIMS AS ITS VOTER?
  -- `homeOf` picks one endpoint per node (`proj₁ (endpointsOf n)`), so this is a
  -- well-defined test, and `nodeOf` takes the blob's voter back to a node.
  atVoter : Link × Dir → VoteBlob → Bool
  atVoter ld v = ⌊ ld ≟ homeOf (nodeOf (blobVoter v)) ⌋

  ------------------------------------------------------------------------
  -- WHY THE GATE IS NOT VACUOUS, ∀-TOPOLOGY
  --
  -- The control exhibits a foreign-voter deposit being refused at ONE instance.
  -- These four lemmas say the same thing for EVERY `Params`, every topology and every
  -- node, so the theorem's content does not rest on the control.
  ------------------------------------------------------------------------

  -- a node's HOME endpoint really is its own: `endpoints-sound` at the head of its
  -- incidence list, which is what `NodeLogic.homeOf` picks
  -- `endpoints-sound` with the direction SPLIT FIRST.  The record's derived `endAt` is an
  -- extended lambda, which only reduces at a CONCRETE direction, so the law's conclusion
  -- at an abstract `d` is a stuck term that does not unify with `endAtT l d`
  -- (measured `UnequalTerms`).  `Topology.agda:225-227` makes exactly this move for
  -- exactly this reason.
  sound-at : ∀ n l d → (l , d) ∈ endpointsList n → endAtT l d ≡ n
  sound-at n l lo mem = endpoints-sound n l lo mem
  sound-at n l hi mem = endpoints-sound n l hi mem

  home-own : ∀ n → endAtT (proj₁ (homeOf n)) (proj₂ (homeOf n)) ≡ n
  home-own n = sound-at n (proj₁ (homeOf n)) (proj₂ (homeOf n)) (here refl)

  -- … hence `homeOf` is INJECTIVE: an endpoint belongs to at most one node
  homeOf-inj : ∀ {n m} → homeOf n ≡ homeOf m → n ≡ m
  homeOf-inj {n} {m} eq =
    trans (sym (home-own n))
          (trans (cong (λ ld → endAtT (proj₁ ld) (proj₂ ld)) eq) (home-own m))

  -- the endpoint decision at its OWN goal shape, so that the `with` abstracts the term
  -- it is splitting on (under `atVoter` it would not — the measured `ok-aux` hazard)
  atVoter-off : ∀ (ld : Link × Dir) (k : Node) → (ld ≡ homeOf k → ⊥)
              → ⌊ ld ≟ homeOf k ⌋ ≡ false
  atVoter-off ld k ¬eq with ld ≟ homeOf k
  ... | yes q = ⊥-elim (¬eq q)
  ... | no  _ = refl

  -- THE GATE REALLY BITES: at node `n`'s own deposit endpoint, a blob whose claimed
  -- voter belongs to a DIFFERENT node has `atVoter ≡ false`, so the obligation genuinely
  -- arises there and only a delivery can discharge it.  Every store event of `n`'s logic
  -- is at `homeOf n` (`NodeLogicL`'s event table), so this covers every deposit `n` makes.
  atVoter-bites : ∀ n v → (nodeOf (blobVoter v) ≡ n → ⊥) → atVoter (homeOf n) v ≡ false
  atVoter-bites n v ¬own =
    atVoter-off (homeOf n) (nodeOf (blobVoter v)) (λ q → ¬own (sym (homeOf-inj q)))

  -- `voterOf` IS INJECTIVE, and the proof is its left inverse — so a system-level S2′
  -- owes no separate injectivity premise.  (Recorded because the Task-8 report and the
  -- campaign ledger both claimed the opposite.)  What a system lift DOES still owe is
  -- the ENDPOINT-INDEXED key; see the header.
  voterOf-inj : ∀ {n m} → voterOf n ≡ voterOf m → n ≡ m
  voterOf-inj {n} {m} eq =
    trans (sym (nodeOf-voterOf n)) (trans (cong nodeOf eq) (nodeOf-voterOf m))

  -- IS THIS THE VOTE-DEPOSIT CHANNEL — and if so, AT WHICH ENDPOINT and with which
  -- blob?  The ONE channel dispatch of the discipline: the gate and the carrying
  -- relation both route through it, so each is discharged by a two-clause case on this
  -- `Maybe` instead of a thirty-two-clause alphabet enumeration (`needs-putVote` still
  -- writes that enumeration once, because its conclusion is a Σ about the channel).
  -- The endpoint is kept because S2′'s question is WHOSE ballot this is.
  isPutVote : (at : AnyTypes (Net_Api Payload)) → proj₁ at
            → Maybe ((Link × Dir) × VoteBlob)
  isPutVote (_ , store l d stPutVote) v = just ((l , d) , v)
  isPutVote _                         _ = nothing

  -- WHAT MINTS: a Notify votes delivery, and nothing else.  Each blob the reply carried
  -- becomes a permission to deposit THAT blob.  ENDPOINT-AGNOSTIC (link and direction
  -- are `_`) — see the module header before lifting this to a system.
  blobMints : (at : AnyTypes (Net_Api Payload)) → proj₁ at → List VoteBlob
  blobMints (_ , apiLP _ _ lnpRecvVotes) vs = vs
  blobMints _                            _  = []

  -- IS THIS DEPOSIT LICENSED?  Either it is the node casting its own ballot (the
  -- deposit is at the claimed voter's home endpoint), or the blob came off the wire.
  vouchedAt : List VoteBlob → (Link × Dir) × VoteBlob → Bool
  vouchedAt ms (ld , v) = atVoter ld v ∨ memberOf v ms

  -- WHAT IS GATED: only a vote deposit, and only by `vouchedAt`.  Everything else free.
  blobGate : List VoteBlob → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool
  blobGate ms at a = maybe′ (vouchedAt ms) true (isPutVote at a)

  -- the gate's monotonicity, as a case on `isPutVote`'s answer alone: the left disjunct
  -- does not mention the minted set and the right one is `memberOf`, which is monotone
  gate-mono-aux : ∀ {ms ms′} → ms ⊆ ms′ → (z : Maybe ((Link × Dir) × VoteBlob))
                → maybe′ (vouchedAt ms) true z ≡ true
                → maybe′ (vouchedAt ms′) true z ≡ true
  gate-mono-aux sub nothing         eq = refl
  gate-mono-aux sub (just (ld , v)) eq with ∨-split eq
  ... | inj₁ l = ∨-inl l
  ... | inj₂ r = ∨-inr (memberOf-mono sub r)

  -- MINTING ONLY EVER OPENS THE GATE
  blobGate-mono : ∀ {ms ms′} → ms ⊆ ms′
                → ∀ at a → blobGate ms at a ≡ true → blobGate ms′ at a ≡ true
  blobGate-mono sub at a eq = gate-mono-aux sub (isPutVote at a) eq

  ------------------------------------------------------------------------
  -- The specification S2′ names
  ------------------------------------------------------------------------

  -- the generic carrier at the S2′ discipline.  `OriginSpecT` is renamed rather than
  -- listed: Agda rejects a name that appears in both `using` and `renaming`.
  open OS.Generic.Origin p t apiES VoteBlob decVoteBlob blobMints blobGate blobGate-mono
    using ( Minted; mintedAfter; mintedAfter-⊇; originOffer; OriginSpecAt; specAt-init
          ; OSafe; gateOK; onτ; onEv; noTick; osafe→⊑T )
    renaming (OriginSpecT to BlobSpecT)
    public

  ------------------------------------------------------------------------
  -- The assume-guarantee instance, and the ONE alphabet enumeration
  ------------------------------------------------------------------------

  -- WHAT A DEPOSIT AT ONE ENDPOINT CARRIES: an obligation, but ONLY when the deposit is
  -- NOT at the claimed voter's own home endpoint.  A node casting its own ballot owes
  -- nothing — that asymmetry IS S2′.
  carriesAt : (Link × Dir) × VoteBlob → VoteBlob → Set
  carriesAt (ld , v) w = atVoter ld v ≡ false × v ≡ w

  -- WHAT A LABEL CARRIES: a foreign-voter deposit carries the blob it deposits; nothing
  -- else carries anything.  (This is the `Carries` of the Wf framework — "needs a
  -- justification" — NOT the same thing as `blobMints`.)
  blobCarries : (at : AnyTypes (Net_Api Payload)) → proj₁ at → VoteBlob → Set
  blobCarries at a w = maybe′ (λ z → carriesAt z w) ⊥ (isPutVote at a)

  -- WHAT THE MINTED SET MUST SAY ABOUT A CARRIED BLOB: a neighbour delivered it
  blobWA : Minted → VoteBlob → Set
  blobWA ms v = memberOf v ms ≡ true

  -- the state a label leads to: EXACTLY `OriginSafe`'s `mintedAfter` on a visible
  -- label (definitionally — `mintedAfter at a ms = mints at a ++ ms`), and unchanged
  -- on a τ or a `√`
  blobNext : Label (⊤ {0ℓ}) → Minted → Minted
  blobNext (ev (evl (evLabel X e a))) ms = blobMints (X , e) a ++ ms
  blobNext _                          ms = ms

  -- the minted set only grows
  blobNext-⊆ : ∀ a ms → ms ⊆ blobNext a ms
  blobNext-⊆ (ev (evl (evLabel X e a))) ms = mintedAfter-⊇ (X , e) a
  blobNext-⊆ (ev (√ _))                 ms = λ q → q
  blobNext-⊆ τ                          ms = λ q → q

  -- EVERY CARRYING CHANNEL IS THE VOTE DEPOSIT.  One clause per `Net_Api` constructor
  -- and, under `store`, one per `StoreTag` — 32 in all (18 non-`store` constructors
  -- plus `store` over all 14 `StoreTag`s) — because `isPutVote`'s catch-all does not
  -- reduce until the constructor is known.  This is the whole alphabet tax of S2′, and
  -- it does double duty: `needs-store` and `carries-VS` both fall out of it.
  needs-putVote : ∀ {X} {e : Net_Api Payload X} {a : X} {v} → blobCarries (X , e) a v
                → Σ[ l ∈ Link ] Σ[ d ∈ Dir ]
                    (_≡_ {A = AnyTypes (Net_Api Payload)}
                         (X , e) (StoreCar stPutVote , store l d stPutVote))
  needs-putVote {e = store l d stPutVote}     _  = l , d , refl
  needs-putVote {e = store _ _ stPut}         ()
  needs-putVote {e = store _ _ stGet}         ()
  needs-putVote {e = store _ _ (stGetAt _)}   ()
  needs-putVote {e = store _ _ stPutEB}       ()
  needs-putVote {e = store _ _ (stGetEBAt _)} ()
  needs-putVote {e = store _ _ stPutBody}     ()
  needs-putVote {e = store _ _ (stGetBody _)} ()
  needs-putVote {e = store _ _ stPutTx}       ()
  needs-putVote {e = store _ _ (stGetTxAt _)} ()
  needs-putVote {e = store _ _ (stGetVoteAt _)} ()
  needs-putVote {e = store _ _ stCert}        ()
  needs-putVote {e = store _ _ (stGetTx _)}   ()
  needs-putVote {e = store _ _ (stHasCert _)} ()
  needs-putVote {e = input _ _ _}             ()
  needs-putVote {e = output _ _ _}            ()
  needs-putVote {e = sndmsg _ _ _}            ()
  needs-putVote {e = rcvmsg _ _ _}            ()
  needs-putVote {e = tx _ _ _}                ()
  needs-putVote {e = sndack _ _ _}            ()
  needs-putVote {e = rcvack _ _ _}            ()
  needs-putVote {e = ack _ _ _}               ()
  needs-putVote {e = done _ _ _}              ()
  needs-putVote {e = apiCS _ _ _}             ()
  needs-putVote {e = apiBF _ _ _}             ()
  needs-putVote {e = apiTS _ _ _}             ()
  needs-putVote {e = apiKA _ _ _}             ()
  needs-putVote {e = apiLN _ _ _}             ()
  needs-putVote {e = apiLF _ _ _}             ()
  needs-putVote {e = apiLP _ _ _}             ()
  needs-putVote {e = env _ _ _}               ()
  needs-putVote {e = break _}                 ()

  -- … weakened to the "some store tag" form `OriginLeaves` asks for
  needs-store : ∀ {X} {e : Net_Api Payload X} {a : X} {v} → blobCarries (X , e) a v
              → Σ[ l ∈ Link ] Σ[ d ∈ Dir ] Σ[ m ∈ StoreTag ]
                  (_≡_ {A = AnyTypes (Net_Api Payload)}
                       (X , e) (StoreCar m , store l d m))
  needs-store {X} {e} {a} {v} c with needs-putVote {X} {e} {a} {v} c
  ... | l , d , refl = l , d , stPutVote , refl

  -- THE SHARED LEAVES: the vacuous-leaf lemmas at both carriers, the two guarantee
  -- alphabets and their `Sep`s, and the prototype peer bundle
  open OL.Generic.Leaves p t apiES Minted VoteBlob blobCarries blobWA blobNext
                         _⊆_ ⊆-refl ⊆-trans blobNext-⊆ needs-store

  -- the assume-guarantee carrier at the S2′ discipline …
  open BP.Carrier (Net_Api-≟ {Payload}) Minted VoteBlob blobCarries blobWA
                  blobNext _⊆_ ⊆-trans blobNext-⊆
    using ( OK; lbl; Wf; nowW; stepW; wf-mono; wf-mono-G; wf-Skip; wf-deadlock
          ; Sep; _∪α_; wf-Par; wf-⦀; wf-⦀⋆ )

  -- … and its returning-tree layer, at the SAME arguments, so the two `Wf`s are the
  -- same record
  open BPW.Body (Net_Api-≟ {Payload}) Minted VoteBlob blobCarries blobWA
                blobNext _⊆_ ⊆-refl ⊆-trans blobNext-⊆
    using ( WfR; nowR; stepR; retR; Stable; stable-node; stable-□
          ; wfR-mono; wfR-Ret; wfR-Stop; wfR-Prefix; wfR-Output; wfR-⊓; wfR-□
          ; wfR->>=; wf-loop; wf-loop0; wf-⦀⁺ )

  ------------------------------------------------------------------------
  -- THE BRIDGE
  ------------------------------------------------------------------------

  -- the disjunction closes either way: at the claimed voter's own endpoint by the LEFT
  -- disjunct (no obligation arose), elsewhere by the membership the obligation hands
  -- over.  Written as a case on a NAMED Boolean rather than a `with`, so that nothing
  -- depends on `with`-abstraction finding `atVoter ld v` under a `maybe′`.
  ok-aux : ∀ (ms : Minted) (ld : Link × Dir) (v : VoteBlob) (b : Bool)
         → atVoter ld v ≡ b → (atVoter ld v ≡ false → memberOf v ms ≡ true)
         → atVoter ld v ∨ memberOf v ms ≡ true
  ok-aux ms ld v true  eq g = ∨-inl eq
  ok-aux ms ld v false eq g = ∨-inr (g eq)

  -- `OK` at a vote deposit IS the gate, and at every other channel the gate is `true`
  gate-ok-aux : (ms : Minted) (z : Maybe ((Link × Dir) × VoteBlob))
              → (∀ {w} → maybe′ (λ y → carriesAt y w) ⊥ z → memberOf w ms ≡ true)
              → maybe′ (vouchedAt ms) true z ≡ true
  gate-ok-aux ms nothing         _ = refl
  gate-ok-aux ms (just (ld , v)) g =
    ok-aux ms ld v (atVoter ld v) refl (λ e → g (e , refl))

  -- `OK` at a label IS the gate
  ok→gate : ∀ {X} {e : Net_Api Payload X} {a : X} {ms}
          → (∀ {w} → blobCarries (X , e) a w → blobWA ms w)
          → blobGate ms (X , e) a ≡ true
  ok→gate {X} {e} {a} {ms} f = gate-ok-aux ms (isPutVote (X , e) a) f

  -- A `Wf` FACT ON THE FULL ALPHABET IS AN `OSafe` FACT.  The two carriers agree by
  -- construction: `blobNext` on a visible label IS `mintedAfter`, `OK` at a label IS
  -- the gate (`ok→gate`), and `Wf` on `fullα` guarantees it for every label.  `OSafe`'s
  -- `noTick` comes from `NoRet`, which belongs to the COMPOSITE, not to the peer
  -- bundle, which does return.
  wf→osafe : ∀ {ms} {M : Proc} → Wf fullα ms M → NoRet M → OSafe ms M
  wf→osafe {ms = ms} w nr .gateOK {X} {e} {a} st =
    ok→gate {X} {e} {a} {ms} (nowW w ⊆-refl tt st)
  wf→osafe w nr .onτ    st = wf→osafe (stepW w ⊆-refl st tt) (NoRet.stepNR nr st)
  wf→osafe w nr .onEv   st =
    wf→osafe (stepW w ⊆-refl st (nowW w ⊆-refl tt st)) (NoRet.stepNR nr st)
  wf→osafe w nr .noTick st = noRet→noTick nr st

  ------------------------------------------------------------------------
  -- The twenty-one threads that need no delivery, TRANSPORTED FROM S2
  --
  -- S2's carrying relation is `a ≡ w` at a vote deposit and `⊥` everywhere else; S2′'s
  -- is the same `a ≡ w` under a side condition.  So S2′ carries STRICTLY LESS, and
  -- every `OffersOnly`-vacuity S2 proved of a thread holds here unchanged.
  ------------------------------------------------------------------------

  -- S2′'s obligation implies S2's: drop the endpoint side condition
  carries-VS : ∀ {X} {e : Net_Api Payload X} {a : X} {w}
             → blobCarries (X , e) a w → VSG.voteCarries (X , e) a w
  carries-VS {X} {e} {a} {w} c with needs-putVote {X} {e} {a} {w} c
  ... | l , d , refl = proj₂ c

  -- S2's shared leaves, at S2's OWN carrier data, so that `VSG.oo-*`'s alphabet has a
  -- name here.  Only `noNeed` is used; the `Wf` of this application is S2's, not ours.
  module VSL = OL.Generic.Leaves p t apiES VSG.Minted VoteBlob
                 VSG.voteCarries VSG.voteWA VSG.voteNext
                 _⊆_ ⊆-refl ⊆-trans VSG.voteNext-⊆ VSG.needs-store

  -- hence: a thread confined to S2's vacuous alphabet is confined to S2′'s
  ooB : ∀ {ℓr} {R : Set ℓr} {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
      → OffersOnly VSL.noNeed M → OffersOnly noNeed M
  ooB = OffersOnly-mono (λ { (X , e) a nn c → nn (carries-VS {X} {e} c) })

  -- … and is a `Wf` leaf at every guarantee alphabet and every state
  wf-vs : ∀ {G ms} {M : Proc} → OffersOnly VSL.noNeed M → Wf G ms M
  wf-vs oo = wf-free (ooB oo)

  ------------------------------------------------------------------------
  -- THE TWO CONTENT-BEARING LEAVES
  ------------------------------------------------------------------------

  -- THE ENDPOINT COMPARISON, once the blob's voter is known to be `n`'s.  A separate
  -- lemma with the voter as a VARIABLE: matching `refl` against `blobVoter (mkVoteBlob
  -- …) ≡ voterOf n` directly would unify two neutral terms, and `rewrite` would not see
  -- the projection under `atVoter` either.
  atVoter-at : ∀ n (u : VoterId) → u ≡ voterOf n
             → ⌊ homeOf n ≟ homeOf (nodeOf u) ⌋ ≡ true
  atVoter-at n u refl rewrite nodeOf-voterOf n = ⌊≟⌋-refl (homeOf n)

  -- THE NODE'S OWN BALLOT IS CAST AT ITS OWN ENDPOINT.  `blobVoter-mk` says the blob
  -- the voter builds names `voterOf n`, and `nodeOf-voterOf` takes that back to `n`,
  -- whose home endpoint is where `putVoteEv n` fires.  This is the ONE place both laws
  -- are spent, and it is why the voter owes nothing.
  atVoter-own : ∀ n r → atVoter (homeOf n) (mkVoteBlob (voterOf n) r) ≡ true
  atVoter-own n r =
    atVoter-at n (blobVoter (mkVoteBlob (voterOf n) r)) (blobVoter-mk (voterOf n) r)

  -- `true` is not `false`
  t≢f : true ≡ false → ⊥
  t≢f ()

  -- A DEPOSIT OF THE NODE'S OWN BALLOT AT ITS OWN HOME ENDPOINT CARRIES NOTHING: the
  -- carrying relation demands `atVoter … ≡ false`, which `atVoter-own` refutes.
  own-ok : ∀ n r {w} → carriesAt (homeOf n , mkVoteBlob (voterOf n) r) w → ⊥
  own-ok n r (eqf , _) = t≢f (trans (sym (atVoter-own n r)) eqf)

  -- THE VOTER.  It reads the k-th oldest held RB, blocks at the body of the EB that RB
  -- announces, and deposits `mkVoteBlob (voterOf n) (rbHash b)` — its OWN ballot, at
  -- its OWN home endpoint, so `blobCarries` is empty there and the obligation never
  -- arises.  S2 needed both reads to discharge its gate; S2′ needs neither, and that
  -- difference is exactly the difference between the two theorems.
  wf-voter : ∀ {ms} n → Wf fullα ms (voter n)
  wf-voter n = wf-loop (λ _ _ _ → tt) (λ _ k _ → vbody k) tt
    where
    -- the tail of one pass, once the ranking block is in hand
    vtail : ∀ {s} k (b : Block) → WfR fullα s (λ _ _ → ⊤)
              (maybe′ (λ h → getBodyEv n h ⟶ (λ _ →
                         putVoteEv n ! mkVoteBlob (voterOf n) (rbHash b) ⟶ Ret (suc k)))
                      (Ret (suc k)) (announcedEB b))
    vtail k b with announcedEB b
    ... | nothing = wfR-Ret (λ _ → tt)
    ... | just h  = wfR-Prefix (λ _ _ _ → λ ()) (λ _ _ _ →
                      wfR-Output (λ _ _ c → ⊥-elim (own-ok n (rbHash b) c))
                                 (λ _ _ → wfR-Ret (λ _ → tt)))

    -- one pass of the voting thread
    vbody : ∀ {s} k → WfR fullα s (λ _ _ → ⊤) (voterBody n k)
    vbody k = wfR-Prefix (λ _ _ _ → λ ()) (λ _ b _ → vtail k b)

  -- EVERY DELIVERED BLOB IS DEPOSITED UNCHANGED, and the delivery that carried them
  -- minted each one — so each deposit's obligation, if it arises at all, is discharged
  -- by the right disjunct.  By induction on the delivered list, with `memberOf-mono`
  -- carrying the witness across the growing state.
  wf-putAllVotes : ∀ {s} n′ vs → (∀ {v} → v ∈ vs → memberOf v s ≡ true)
                 → WfR fullα s (λ _ _ → ⊤) (putAllVotes n′ vs)
  wf-putAllVotes n′ []       h = wfR-Ret (λ _ → tt)
  wf-putAllVotes n′ (v ∷ vs) h =
    wfR-Output (λ le _ → λ { (_ , refl) → memberOf-mono le (h (here refl)) })
               (λ le _ → wf-putAllVotes n′ vs (λ q → memberOf-mono le (h (there q))))

  -- THE NOTIFY CLIENT.  Four branches after the long-poll request: an announcement
  -- (nothing), a body offer (deposits a BODY), a tx-closure offer (deposits
  -- TRANSACTIONS) and a votes reply — the only one that deposits a blob, and the one
  -- place `blobMints` fires.
  wf-lnClient : ∀ {ms} n ld → Wf fullα ms (lnClientLoopL n ld)
  wf-lnClient n (l , d) = wf-loop0 (wfR-Prefix (λ _ _ _ → λ ()) (λ _ _ _ → choice))
    where
    -- the announcement branch
    annB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
             (apiLP l d lnpRecvBlockAnnouncement ⟶ (λ _ → Skip))
    annB = wfR-free (OffersOnly-Prefix (λ _ → λ ()) (λ _ → OffersOnly-Skip)) tt

    -- the body-offer branch (S2's vacuity, transported)
    offB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
             (apiLP l d lnpRecvBlockOffer ⟶ fetchBody n l d)
    offB = wfR-free (OffersOnly-Prefix (λ _ → λ ())
                      (λ q → ooB (VSG.oo-fetchBody n l d q))) tt

    -- the tx-closure branch (likewise)
    txB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
            (apiLP l d lnpRecvBlockTxsOffer ⟶ fetchTxs n l d)
    txB = wfR-free (OffersOnly-Prefix (λ _ → λ ())
                     (λ q → ooB (VSG.oo-fetchTxs n l d q))) tt

    -- the votes branch: deposit exactly the blobs the reply carried, which that very
    -- reply minted
    votB : ∀ {s} → WfR fullα s (λ _ _ → ⊤) (apiLP l d lnpRecvVotes ⟶ putAllVotes n)
    votB = wfR-Prefix (λ _ _ _ → λ ()) (λ _ vs _ →
             wf-putAllVotes n vs (λ q → ∈→memberOf _ _ (∈-++⁺ˡ q)))

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

  -- one endpoint's ten threads
  wf-endpoint : ∀ {ms} n e → Wf fullα ms (endpointThreadsL n e)
  wf-endpoint n e =
    wf-⦀ (wf-vs (VSG.oo-clientLoop n e))
      (wf-⦀ (wf-vs (VSG.oo-serverLoopL n e))
      (wf-⦀ (wf-lnClient n e)
      (wf-⦀ (wf-vs (VSG.oo-lnServerLoopL n e))
      (wf-⦀ (wf-vs (VSG.oo-bodyOfferLoop n e))
      (wf-⦀ (wf-vs (VSG.oo-voteOfferLoop n e))
      (wf-⦀ (wf-vs (VSG.oo-ebServeLoop n e))
      (wf-⦀ (wf-vs (VSG.oo-ebTxsServeLoop n e))
      (wf-⦀ (wf-vs (VSG.oo-tsPull n e)) (wf-vs (VSG.oo-tsServe n e))))))))))

  -- every incident endpoint's threads
  wf-allThreads : ∀ {ms} n → Wf fullα ms (allThreadsL n)
  wf-allThreads n =
    wf-⦀⁺ (endpointThreadsL n) (proj₁ (endpointsOf n)) (proj₂ (endpointsOf n))
          (λ e → wf-endpoint n e)

  -- the six node-level threads and every endpoint's ten
  wf-threads : ∀ {ms} n
             → Wf fullα ms (forgeL n ⦀ (forgeCert n ⦀ (ebIndex n ⦀ (voter n ⦀
                              (submit n ⦀ (certSink n ⦀ allThreadsL n))))))
  wf-threads n =
    wf-⦀ (wf-vs (VSG.oo-forgeL n))
      (wf-⦀ (wf-vs (VSG.oo-forgeCert n))
      (wf-⦀ (wf-vs (VSG.oo-ebIndex n))
      (wf-⦀ (wf-voter n)
      (wf-⦀ (wf-vs (VSG.oo-submit n))
      (wf-⦀ (wf-vs (VSG.oo-certSink n)) (wf-allThreads n))))))

  -- A GATE-CARRYING THREAD GROUP AGAINST ANY STORE GROUP.  The threads carry the gate,
  -- the stores guarantee nothing, and the one key-needing channel is inside `storeES`,
  -- so `Sep` asks the stores for nothing.  Stated for an ARBITRARY thread and store
  -- operand so that the negative control's reduced composite uses the same lemma.
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
  -- bundle — the same builder `LeiosInstanceL.leiosSystemL` composes the system from
  nodeP : Node → Proc → Proc
  nodeP = nodeWith nodeBundleP

  -- S2′ — BLOB ORIGIN, node-local.  A node running `nodeLogicL` from empty stores never
  -- deposits a vote blob attributed to ANOTHER voter unless a neighbour delivered that
  -- exact blob on `lnpRecvVotes`; blobs it casts itself are attributed to itself.  So
  -- relayed blobs have an origin and the node invents no ballot in another's name.
  -- LEVEL: node.  It says nothing about what other nodes do, and nothing about whether
  -- the claimed voter really cast the blob at ITS node — that is a network-wide
  -- statement and is NOT proved here.
  BlobSound : Set₁
  BlobSound = ∀ (n : Node) → BlobSpecT ⊑T nodeP n (nodeLogicL n st₀)

  -- S2′ FOR ANY NODE LOGIC THAT CARRIES THE GATE AND NEVER RETURNS.  The bundle and the
  -- logic compose on `apiES` at the full guarantee alphabet (`Sep apiES` is trivial
  -- there), and `wf→osafe` then `osafe→⊑T` turn that one `Wf` fact into the trace
  -- refinement.  The logic is a PARAMETER so that the negative control's comparison
  -- runs through exactly this assembly.
  soundOf : ∀ n (lg : Proc) → Wf fullα [] lg → NoRet lg → BlobSpecT ⊑T nodeP n lg
  soundOf n lg w nr =
    osafe→⊑T (wf→osafe (wf-mono-G (λ _ _ _ → inj₁ tt)
                         (wf-Par apiES sep-api (wf-linkBundlesP n) w))
                       (NoRet-ParR apiES nr))

  -- S2′, PROVED, at the shipped node logic from empty stores
  blobSound : BlobSound
  blobSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)

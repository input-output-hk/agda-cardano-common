{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S5, TRANSACTION ORIGIN: a node puts a
-- transaction in its MEMPOOL only if the environment handed it that very
-- transaction, or it ASKED FOR that transaction's hash on the wire.
--
-- WHAT S5 SAYS.  A node running `nodeLogicL` from empty stores performs
-- `store home(n) stPutTx ! tx` only when `txHash tx` is
--
--   * the hash of a transaction the environment submitted to it at
--     `env … envSubmit` — the node was handed that transaction; or
--   * one of the ids the node ITSELF asked for at
--     `apiTS l d sendTSRequestTxsPipelined` — a TxSubmission pull; or
--   * one of the hashes the EB body table names for the point the node
--     ITSELF requested the tx closure of, at
--     `apiLP l d lfpSendBlockTxsRequest`.
--
-- IN ONE SENTENCE, AND THIS IS THE QUOTABLE FORM: node `n`, running the full
-- real `nodeLogicL` from empty stores inside its prototype peer bundle,
-- never performs `store home(n) stPutTx ! tx` unless an earlier event of the
-- same trace was an `env … envSubmit` carrying that transaction, an
-- `apiTS … sendTSRequestTxsPipelined` whose id list contains `txHash tx`, or
-- an `apiLP … lfpSendBlockTxsRequest` for a point whose EB body table names
-- `txHash tx` — saying nothing about whether the request was wise, whether a
-- hash-colliding transaction was substituted, how long or how often one
-- request keeps licensing deposits, or about any other store.
--
-- ============ TWO HONEST LIMITS.  READ BEFORE QUOTING S5. ============
--
-- (1) NO TRANSACTION IN THIS MODEL EVER REACHES CONSENSUS, so S5 IS A
--     DIFFUSION-HYGIENE STATEMENT AND NOT THE ANALOGUE OF S1.  `ebTxs` is a
--     `LeiosParams` FIELD (`LeiosParams.agda:69-74`), fixed independently of
--     any node's mempool, and nothing anywhere builds an EB or a ranking
--     block out of `Mem`.  The mempool's only two readers are wire servers —
--     `tsServeBody` (via `stGetTxAt`) and `serveTxs` (via `stGetTx`) — so a
--     transaction goes mempool → wire → mempool and stops.  S1 guards the
--     store the VOTER actually reads; S5 guards a store nothing in the model
--     consumes except to re-diffuse it.  Never present the two as peers.
--
-- (2) THE KEY SPACE SATURATES AT THE SHIPPED LINE.  `LeiosInstanceL` takes
--     `Tx = TxHash = Bool` with `txHash = id`, so the whole per-endpoint key
--     space is TWO keys and two `env … envSubmit` events mint all of it: at
--     the shipped instance the window S5 constrains is two events wide.  The
--     theorem stays non-vacuous ∀-`Params` and the control still bites, but
--     the shipped-line window is small.  THIS IS PARITY WITH S1, NOT A NEW
--     DEFECT — `EBHash = Bool` too, so S1's forge mint saturates identically.
--
-- WHAT S5 DOES **NOT** RULE OUT — ALSO READ BEFORE QUOTING IT.
--   * It says nothing about whether the transaction the node asked for is one
--     it should have asked for: any id a TxSubmission reply offers may be
--     requested, and a request MINTS.  S5 is a "no unsolicited transactions"
--     statement, not a validity one — the prototype has no notion of a valid
--     transaction at all, and nothing validates.
--   * `txHash` IS NOWHERE ASSUMED INJECTIVE, so the two wire guards fix the
--     HASH and not the CONTENT: a peer that answers with different content
--     colliding on a requested hash passes `memberOf (txHash tx) ids` /
--     `⌊ txHash tx ≟ k ⌋` and its transaction is stored.
--   * THE MINTED SET IS APPEND-ONLY AND UNPAIRED (`mintedAfter at a ms =
--     mints at a ++ ms`): a permission, once granted, is permanent and is
--     never consumed by the deposit that spends it.  So ONE request licenses
--     UNBOUNDEDLY MANY later deposits of those hashes, at any endpoint of
--     that node and at any later time.  S5 is "every deposit has an earlier
--     origin", not "one request, one deposit".
--   * It says nothing about the block store (`stPut`), the EB-body store
--     (`stPutBody`), the EB-entry store (`stPutEB`) or the vote store
--     (`stPutVote`) — those are S4, S1, nobody's and S2's business.
--   * It says nothing about OTHER nodes: it is a NODE-level statement about
--     one node's own logic inside its own peer bundle, and
--     `Leios.TxSystemL` is what lifts it to the network.
--   * It is purely safety-shaped.  No module here, or anywhere in this
--     estate, exhibits a GOOD node actually reaching `stPutTx`; S5 therefore
--     constrains nothing the shipped system is shown to DO.
--   * IT IS A NEW THEOREM, so there is no "no weaker than the old one"
--     comparison to make — unlike S1/S2′/S3 there was no endpoint-blind
--     predecessor to compare against.
--
-- THE DISCIPLINE IS ENDPOINT-INDEXED, AND THAT IS WHAT LETS IT LIFT.  The key
-- is a transaction hash TOGETHER WITH THE DEPOSIT ENDPOINT it licenses
-- (`TxKey = (Link × Dir) × TxHash`, so `Minted = List TxKey`).  An
-- `env l d envSubmit` carrying `tx` mints `((l , d) , txHash tx)` — node-local,
-- since `submitEv n` fires at `homeOf n`, which is also where `putTxEv n`
-- fires, so record η closes that half definitionally.  The two WIRE mints are
-- PER-ENDPOINT and are normalised to the depositing endpoint, because a node
-- requests at every incident endpoint but deposits only at `homeOf n`.  The
-- two normalisations are DIFFERENT, and that is `NodeLogicL`'s DIRECTION RULE
-- and not a choice:
--   * `lnClientLoopL` drives `d` (it talks to a CLIENT peer), so its
--     `apiLP l d lfpSendBlockTxsRequest` is owned by `endAt l d` and the mint
--     is keyed by `homeAt (l , d)`;
--   * `tsPull` drives `opposite d` (the TxSubmission REQUESTER is a SERVER
--     peer), so `apiTS l d sendTSRequestTxsPipelined` is owned by
--     `endAt l (opposite d)` and the mint is keyed by `homeOpp (l , d)`.
-- Neither channel has any other user in `nodeLogicL`, so each normalisation
-- names exactly the node whose thread drives it; `homeOf` is injective
-- (`homeOf-inj`), so a request at node X mints no key any deposit of node Y
-- can spend, and `Leios.TxSystemL` spends exactly that.
--
-- HOW IT IS PROVED.  The assume-guarantee route S1/S2/S2′ take —
-- `BlockProvenance.Carrier` plus `BlockProvenanceWfR.Body`, the shared leaves
-- of `OriginLeaves`, and `wf→osafe` back into `OriginSafe`.  THE GATED
-- CHANNEL IS EMITTED BY A THREAD (`submit`, `putAllTx` inside `tsPull`, and
-- `putChecked` inside the Notify client), never by a store, so this is S1's
-- ORIENTATION: the thread group carries `fullα`, the store group `∅α`, the
-- `Sep` is `sep-store`, and the assembly is `wf-withStores`.
--
-- ALL THREE MINT CLAUSES CARRY WEIGHT, AND TWO OF THEM CARRY CONTENT.
--   * `envSubmit` is SELF-LICENSING bookkeeping: `submit` deposits that very
--     transaction one step later.  It cannot be dropped — all three deposit
--     routes share the `stPutTx` channel and the gate is per-channel, so
--     without this clause `submit`'s own deposit is unprovable.
--   * `sendTSRequestTxsPipelined` is CONTENT.  `putAllTx`'s guard
--     `memberOf (txHash tx) ids` — added by commit `0c2d3e63` — is what
--     discharges `wf-tsPull`'s leaf; delete the guard and the leaf is
--     unprovable, because an arbitrary delivered transaction's hash need not
--     be in `ids`.
--   * `lfpSendBlockTxsRequest` is CONTENT.  `putChecked`'s guard
--     `⌊ txHash tx ≟ k ⌋`, with `k` read out of `at? o (ebTxs h)` at the very
--     point `h` the request named, is what discharges `wf-lnClient`'s leaf;
--     delete it and the leaf is unprovable, which `Leios.TxOriginBad`
--     machine-checks as an actual refutation.
-- NEITHER REPLY MINTS (`recvTSReplyTxs`, `lfpRecvBlockTxs`).  Minting at a
-- reply would licence whatever the reply happens to carry and delete the
-- theorem — the same trap `BodyOrigin` records for `lfpRecvBlock`, here twice
-- over.
--
-- THE VACUITY ALPHABET IS S5'S OWN.  `BodyOrigin.noPuts` excludes `stPut` and
-- `stPutBody`, for S1 and S4, and says nothing about `stPutTx`; `noTxPut`
-- below is the analogue.  It buys more here than `noPuts` does there: S5
-- gates NO channel the forge thread touches, so `forgeL` — content-bearing
-- for both S1 and S4 — is a one-line vacuity for S5, and so is `fetchBody`.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.TxOrigin where

open import Level using (Level; 0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-map⁺)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

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

-- the S5 origin discipline, parametric in the network parameters, the Leios
-- parameters, the topology, the api alphabet and the node-to-voter map — exactly the
-- five parameters `NodeLogicL.Generic` takes, so `nodeLogicL` below is literally its
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open Params p
    using ( Block; LSlot; VoterId; VoteBlob; EB; EBHash; Tx; TxHash; Size
          ; linkConfig; ebHash; rbHash; txHash; slotOf; announcedEB
          ; decBlock; decEBHash; decLSlot; decVoteBlob; decEB; decTx; decTxHash )
  open LeiosP p using (LeiosEb; LeiosPoint; DecEq-LeiosPoint; allOffsets)
  open LeiosP.LeiosParams lp using (mkVoteBlob; ebTxs; ebSize; rbCert)
  -- EVERY tag named below MUST appear here: an unlisted tag silently becomes a pattern
  -- VARIABLE and the carrier table turns into a stuck term (campaign ledger, gotcha 1).
  open N p
    using ( Link; Net_Api; Net_Api-≟; StoreTag; StoreCar
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; apiLP; store; env; break
          ; stPut; stGet; stGetAt; stPutEB; stGetEBAt; stPutBody; stGetBody
          ; stPutTx; stGetTxAt; stGetTx; stPutVote; stGetVoteAt; stCert; stHasCert
          ; envForge; envSubmit
          ; lnpSendBlockOffer; lnpSendBlockTxsOffer
          ; lnpRecvBlockAnnouncement; lnpRecvBlockOffer; lnpRecvBlockTxsOffer
          ; lnpRecvVotes
          ; lfpSendBlockRequest; lfpSendBlockTxsRequest; lfpSendBlock; lfpSendBlockTxs
          ; lfpRecvBlock; lfpRecvBlockTxs; lfpReqBlockRequest; lfpReqBlockTxsRequest
          ; sendTSRequestTxsPipelined )
  -- `Tx`/`TxHash` come from `Params`; `DecEq-Tx` is deliberately NOT opened from `Data`,
  -- so `decTxHash` is the ONE `DecEq TxHash` in scope and instance search resolves exactly
  -- the term `NodeLogicL`'s `memberOf` and `putChecked`'s `_≟_` were built with (ledger
  -- gotcha 4).  Those two are what S5's content leaves decide on.
  open D p
    using ( Payload; Point; Header; Tip; Vote; point; header; vote; TxBitmap
          ; DecEq-Point; DecEq-Header; DecEq-Tip; DecEq-ChainRange; DecEq-Payload
          ; DecEq-Vote; DecEq-EBPoint; DecEq-TxBitmap; DecEq-TxEntries
          ; DecEq-TxsRequest; DecEq-TxsReply; DecEq-Offer )
  -- (wholesale, as `NetworkPar` and `OriginLeaves`: `Dir`, its decidable equality and
  -- the six `IDs` constructors)
  open import Cardano_network.Base
  open Topology t using (Node; endpointsOf; endpointsList; endpoints-sound)
  -- `endAt` is NOT opened: the record's derived `endAt` is a pattern-matching lambda, and
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
    using ( Alpha; OffersOnly; OffersOnly-mono; NoRet
          ; OffersOnly-Ret; OffersOnly-Skip; OffersOnly-Prefix; OffersOnly-Prefix₀
          ; OffersOnly-Output; OffersOnly->>=; OffersOnly-loop; OffersOnly-loop0
          ; NoRet-Par; NoRet-⦀; NoRet-loop0 )
  -- the right-sided `NoRet`: a node puts its TERMINATING peer bundle on the LEFT of
  -- `∥⇘ apiES ⇙`, and `DRCongruenceRep.NoRet-Par` reads the left operand
  open BPS.Generic p t apiES using (NoRet-ParR)
  open NL.Generic p t apiES
    using (storeES; homeOf; forgeEv; putEv; clientLoop; clientBody-k; serverBody-k)
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
  open OS using (memberOf; memberOf-mono; memberOf→∈; ∈→memberOf)
  open OS.Generic p t apiES using (noRet→noTick)
  -- the PROTOTYPE peer bundle, whose nine `Wf` facts live in `OriginLeaves.Leaves`
  open import Cardano_network.Parametric.Leios.PeersP p using (nodeBundleP)

  instance
    -- product `DecEq` for the `sendCSRollForward` carrier (`Header × Tip`) — the same
    -- instance `NodeLogic` declares, so `OffersOnly-Output` sees the one the `!`-output
    -- in `serverBody-k` was built with (`BodyOrigin` does the same)
    DecEq-Header×Tip : DecEq (Header × Tip)
    DecEq-Header×Tip = DecEqI.DecEq-×

  ------------------------------------------------------------------------
  -- THE MINTED KEY, AND THE ENDPOINT BOOKKEEPING IT NEEDS
  ------------------------------------------------------------------------

  -- the endpoint equality, assembled out of the QUALIFIED `Fin` and `Dir` instances.
  -- Deliberately not an instance declaration: a product instance at this type would
  -- compete with the ones `wfR-Output` resolves its `DecEq X` to (campaign ledger,
  -- gotcha 4).  `CertSound.ld-≟` and `BodyOrigin.ld-≟` are the precedents.
  ld-≟ : (x y : Link × Dir) → Dec (x ≡ y)
  ld-≟ = ≡-dec (DecEq._≟_ DecEqI.DecEq-Fin) (DecEq._≟_ DecEq-Dir)

  -- THE MINTED KEY: A TRANSACTION HASH TOGETHER WITH THE DEPOSIT ENDPOINT IT LICENSES.
  -- The endpoint index is what makes the discipline sound at a composite of SEVERAL
  -- nodes: without it a request sent at node X would licence a mempool deposit at node Y.
  TxKey : Set
  TxKey = (Link × Dir) × TxHash

  -- the key's equality, likewise explicit rather than an instance
  decTxKey : DecEq TxKey
  decTxKey = record { _≟_ = ≡-dec ld-≟ (DecEq._≟_ decTxHash) }

  -- is this key in the minted set?  `OriginSafe.memberOf` at the equality above, passed
  -- explicitly because `memberOf` takes its `DecEq` as an INSTANCE argument and
  -- `decTxKey` is not one
  memKey : TxKey → List TxKey → Bool
  memKey k ms = memberOf ⦃ decTxKey ⦄ k ms

  -- … monotone in the minted set, which is what keeps the gate monotone
  memKey-mono : ∀ {k ms ms′} → ms ⊆ ms′ → memKey k ms ≡ true → memKey k ms′ ≡ true
  memKey-mono sub eq = memberOf-mono ⦃ decTxKey ⦄ sub eq

  -- … and implied by propositional membership
  ∈→memKey : ∀ k ms → k ∈ ms → memKey k ms ≡ true
  ∈→memKey k ms q = ∈→memberOf ⦃ decTxKey ⦄ k ms q

  -- THE MEMPOOL'S OWN BOOLEAN MEMBERSHIP TEST REFLECTS PROPOSITIONAL MEMBERSHIP.
  -- `NodeLogicL.memberOf` is DEFINITIONALLY `OriginSafe.memberOf` at `decTxHash` (the
  -- only `DecEq TxHash` in either scope), so that module's lemma applies verbatim; the
  -- wrapper exists so the instance is written once and the list is always pinned.
  memNL→∈ : ∀ (x : TxHash) (xs : List TxHash) → memberOfNL x xs ≡ true → x ∈ xs
  memNL→∈ x xs eq = memberOf→∈ ⦃ decTxHash ⦄ x xs eq

  -- THE `at?` LEMMA S5 NEEDS AND NOTHING ELSE IN THE REPO HAS: the item an offset names
  -- really is in the list.  `putChecked` reads its expected hash out of
  -- `at? o (ebTxs h)`, and only this transports that hash into the minted key list.
  at?-∈ : ∀ {A : Set} (o : ℕ) (xs : List A) {x : A} → at? o xs ≡ just x → x ∈ xs
  at?-∈ _       []       ()
  at?-∈ zero    (y ∷ ys) refl = here refl
  at?-∈ (suc o) (y ∷ ys) eq   = there (at?-∈ o ys eq)

  -- `endpoints-sound` with the direction SPLIT FIRST.  The record's derived `endAt` is an
  -- extended lambda, which only reduces at a CONCRETE direction, so the law's conclusion
  -- at an abstract `d` is a stuck term that does not unify with `endAtT l d`
  -- (`BodyOrigin.sound-at` and `Topology.agda:225-227` make exactly this move).
  sound-at : ∀ n l d → (l , d) ∈ endpointsList n → endAtT l d ≡ n
  sound-at n l lo mem = endpoints-sound n l lo mem
  sound-at n l hi mem = endpoints-sound n l hi mem

  -- `opposite` is INVOLUTIVE.  Needed because the TxSubmission pull thread of endpoint
  -- `(l , d)` drives direction `opposite d`, so the mint it spends is normalised through
  -- one `opposite` and reached through another.
  opposite-invol : ∀ d → opposite (opposite d) ≡ d
  opposite-invol lo = refl
  opposite-invol hi = refl

  -- … hence the soundness law at the DOUBLY opposed direction, which is the form the
  -- TxSubmission leaf meets
  sound-opp : ∀ n l d → (l , d) ∈ endpointsList n → endAtT l (opposite (opposite d)) ≡ n
  sound-opp n l d mem =
    subst (λ z → endAtT l z ≡ n) (sym (opposite-invol d)) (sound-at n l d mem)

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

  -- THE DEPOSIT ENDPOINT A REQUEST SENT AT ONE ENDPOINT LICENSES: the home endpoint of
  -- the node that owns the sending endpoint.  A node sends at EVERY endpoint incident to
  -- it but deposits only at `homeOf n` (`NodeLogicL.putTxEv`), so a mint keyed by the
  -- sending endpoint itself would licence nothing at a node of degree > 1.  This is the
  -- normalisation for the channels a thread drives at `d` — the Notify client's.
  homeAt : Link × Dir → Link × Dir
  homeAt ld = homeOf (endAtT (proj₁ ld) (proj₂ ld))

  -- … AND THE MIRROR, for the channels a thread drives at `opposite d`.  `tsPull` talks
  -- to the TxSubmission REQUESTER, which `Node.bundleAt` puts at `opposite d`
  -- (`NodeLogicL`'s DIRECTION RULE), so the node that owns
  -- `apiTS l d sendTSRequestTxsPipelined` is the one at the OTHER end of the direction
  -- flag.  No other thread drives that channel, so this names exactly one node.
  homeOpp : Link × Dir → Link × Dir
  homeOpp ld = homeOf (endAtT (proj₁ ld) (opposite (proj₂ ld)))

  ------------------------------------------------------------------------
  -- The origin discipline
  ------------------------------------------------------------------------

  -- IS THIS THE MEMPOOL-DEPOSIT CHANNEL, and if so which transaction?  The ONE channel
  -- dispatch of the discipline: the gate and the carrying relation both route through it,
  -- so each is discharged by a two-clause case on this `Maybe` instead of a
  -- thirty-two-clause alphabet enumeration (`needs-putTx` still writes that enumeration
  -- once, because its conclusion is a Σ about the channel).  The ENDPOINT is kept,
  -- because the key the deposit demands is indexed by it.
  isPutTx : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Maybe ((Link × Dir) × Tx)
  isPutTx (_ , store l d stPutTx) tx′ = just ((l , d) , tx′)
  isPutTx _                       _   = nothing

  -- THE KEYS A TX-CLOSURE REQUEST MINTS: one per entry of the EB body table of the point
  -- requested, at the deposit endpoint `ld`.  A plain `map` with `proj₁`, never a
  -- pattern-matching lambda — at a variable key the latter blocks and the `⁺`/`⁻`
  -- membership lemmas fail (campaign ledger).
  tableKeys : (Link × Dir) → EBHash → List TxKey
  tableKeys ld h = map (λ e → (ld , proj₁ e)) (ebTxs h)

  -- WHAT MINTS.  Three clauses, and all three are needed because all three deposit routes
  -- share the ONE `stPutTx` channel:
  --   * a SUBMISSION carrying `tx` mints that transaction's hash at the submitting
  --     endpoint — self-licensing bookkeeping, since `submit` deposits that very `tx` one
  --     step later, and node-local because `submitEv n` fires at `homeOf n`;
  --   * a TxSubmission TX REQUEST mints every id it asked for, at the requesting node's
  --     own deposit endpoint (`homeOpp`, because the requester runs at `opposite d`);
  --   * a TX-CLOSURE REQUEST mints every hash the EB body table of the requested point
  --     names, at the requesting node's own deposit endpoint (`homeAt`, because the
  --     Notify client runs at `d`).
  -- NEITHER REPLY MINTS (`recvTSReplyTxs`, `lfpRecvBlockTxs`): minting at a reply would
  -- licence whatever the reply carries and delete the theorem.
  txMints : (at : AnyTypes (Net_Api Payload)) → proj₁ at → List TxKey
  txMints (_ , env   l d envSubmit)                tx′ = ((l , d) , txHash tx′) ∷ []
  txMints (_ , apiTS l d sendTSRequestTxsPipelined) ids =
    map (λ h → (homeOpp (l , d) , h)) ids
  txMints (_ , apiLP l d lfpSendBlockTxsRequest)   qbm =
    tableKeys (homeAt (l , d)) (proj₁ (proj₁ qbm))
  txMints _                                        _   = []

  -- IS THIS DEPOSIT LICENSED?  The transaction's hash must have been submitted or
  -- requested here, FOR THIS VERY DEPOSIT ENDPOINT.
  vouched : List TxKey → (Link × Dir) × Tx → Bool
  vouched ms (ld , tx′) = memKey (ld , txHash tx′) ms

  -- WHAT IS GATED: only a mempool deposit, and only by `vouched`.  Everything else is
  -- free — in particular every other store deposit (see the module header).
  txGate : List TxKey → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool
  txGate ms at a = maybe′ (vouched ms) true (isPutTx at a)

  -- the gate's monotonicity, as a case on `isPutTx`'s answer alone: the only
  -- state-dependent test is `memKey`, which is monotone
  gate-mono-aux : ∀ {ms ms′} → ms ⊆ ms′ → (z : Maybe ((Link × Dir) × Tx))
                → maybe′ (vouched ms) true z ≡ true
                → maybe′ (vouched ms′) true z ≡ true
  gate-mono-aux sub nothing           eq = refl
  gate-mono-aux sub (just (ld , tx′)) eq = memKey-mono sub eq

  -- MINTING ONLY EVER OPENS THE GATE
  txGate-mono : ∀ {ms ms′} → ms ⊆ ms′
              → ∀ at a → txGate ms at a ≡ true → txGate ms′ at a ≡ true
  txGate-mono sub at a eq = gate-mono-aux sub (isPutTx at a) eq

  ------------------------------------------------------------------------
  -- The specification S5 names
  ------------------------------------------------------------------------

  -- the generic carrier at the S5 discipline.  `OriginSpecT` is renamed rather than
  -- listed: Agda rejects a name that appears in both `using` and `renaming`.
  open OS.Generic.Origin p t apiES TxKey decTxKey txMints txGate txGate-mono
    using ( Minted; mintedAfter; mintedAfter-⊇; originOffer; OriginSpecAt; specAt-init
          ; OSafe; gateOK; onτ; onEv; noTick; osafe→⊑T )
    renaming (OriginSpecT to TxSpecT)
    public

  ------------------------------------------------------------------------
  -- The assume-guarantee instance, and the ONE alphabet enumeration
  ------------------------------------------------------------------------

  -- WHAT A DEPOSIT AT ONE ENDPOINT CARRIES: an obligation keyed by the transaction's hash
  -- AND the endpoint the deposit is made at
  carriesAt : (Link × Dir) × Tx → TxKey → Set
  carriesAt (ld , tx′) k = (ld , txHash tx′) ≡ k

  -- WHAT A LABEL CARRIES: a mempool deposit carries the hash of the transaction it
  -- deposits KEYED BY THE ENDPOINT IT IS DEPOSITED AT; nothing else carries anything.
  -- (This is the `Carries` of the Wf framework — "needs a justification" — NOT `txMints`.)
  -- CONFINED TO `store _ _ stPutTx`, which is what keeps `OriginLeaves`' `carries-store`
  -- premise true and the whole `fullα` fold cheap.
  txCarries : (at : AnyTypes (Net_Api Payload)) → proj₁ at → TxKey → Set
  txCarries at a k = maybe′ (λ z → carriesAt z k) ⊥ (isPutTx at a)

  -- WHAT THE MINTED SET MUST SAY ABOUT A CARRIED KEY: that hash was submitted or
  -- requested here, for that very deposit endpoint
  txWA : Minted → TxKey → Set
  txWA ms k = memKey k ms ≡ true

  -- the state a label leads to: EXACTLY `OriginSafe`'s `mintedAfter` on a visible label
  -- (definitionally — `mintedAfter at a ms = mints at a ++ ms`), unchanged on τ and `√`
  txNext : Label (⊤ {0ℓ}) → Minted → Minted
  txNext (ev (evl (evLabel X e a))) ms = txMints (X , e) a ++ ms
  txNext _                          ms = ms

  -- the minted set only grows
  txNext-⊆ : ∀ a ms → ms ⊆ txNext a ms
  txNext-⊆ (ev (evl (evLabel X e a))) ms = mintedAfter-⊇ (X , e) a
  txNext-⊆ (ev (√ _))                 ms = λ q → q
  txNext-⊆ τ                          ms = λ q → q

  -- EVERY CARRYING CHANNEL IS THE MEMPOOL DEPOSIT.  One clause per `Net_Api` constructor
  -- and, under `store`, one per `StoreTag` — 32 clauses in all (18 non-`store`
  -- constructors plus 14 `StoreTag`s), of which 31 are absurd — because `isPutTx`'s
  -- catch-all does not reduce until the constructor is known.  This is the whole alphabet
  -- tax of S5, and it does double duty: `needs-store` and `nTP→noNeed` both fall out of it.
  needs-putTx : ∀ {X} {e : Net_Api Payload X} {a : X} {k} → txCarries (X , e) a k
              → Σ[ l ∈ Link ] Σ[ d ∈ Dir ]
                  (_≡_ {A = AnyTypes (Net_Api Payload)}
                       (X , e) (StoreCar stPutTx , store l d stPutTx))
  needs-putTx {e = store l d stPutTx}         _  = l , d , refl
  needs-putTx {e = store _ _ stPut}           ()
  needs-putTx {e = store _ _ stGet}           ()
  needs-putTx {e = store _ _ (stGetAt _)}     ()
  needs-putTx {e = store _ _ stPutEB}         ()
  needs-putTx {e = store _ _ (stGetEBAt _)}   ()
  needs-putTx {e = store _ _ stPutBody}       ()
  needs-putTx {e = store _ _ (stGetBody _)}   ()
  needs-putTx {e = store _ _ (stGetTxAt _)}   ()
  needs-putTx {e = store _ _ stPutVote}       ()
  needs-putTx {e = store _ _ (stGetVoteAt _)} ()
  needs-putTx {e = store _ _ stCert}          ()
  needs-putTx {e = store _ _ (stGetTx _)}     ()
  needs-putTx {e = store _ _ (stHasCert _)}   ()
  needs-putTx {e = input _ _ _}               ()
  needs-putTx {e = output _ _ _}              ()
  needs-putTx {e = sndmsg _ _ _}              ()
  needs-putTx {e = rcvmsg _ _ _}              ()
  needs-putTx {e = tx _ _ _}                  ()
  needs-putTx {e = sndack _ _ _}              ()
  needs-putTx {e = rcvack _ _ _}              ()
  needs-putTx {e = ack _ _ _}                 ()
  needs-putTx {e = done _ _ _}                ()
  needs-putTx {e = apiCS _ _ _}               ()
  needs-putTx {e = apiBF _ _ _}               ()
  needs-putTx {e = apiTS _ _ _}               ()
  needs-putTx {e = apiKA _ _ _}               ()
  needs-putTx {e = apiLN _ _ _}               ()
  needs-putTx {e = apiLF _ _ _}               ()
  needs-putTx {e = apiLP _ _ _}               ()
  needs-putTx {e = env _ _ _}                 ()
  needs-putTx {e = break _}                   ()

  -- … weakened to the "some store tag" form `OriginLeaves` asks for
  needs-store : ∀ {X} {e : Net_Api Payload X} {a : X} {k} → txCarries (X , e) a k
              → Σ[ l ∈ Link ] Σ[ d ∈ Dir ] Σ[ m ∈ StoreTag ]
                  (_≡_ {A = AnyTypes (Net_Api Payload)}
                       (X , e) (StoreCar m , store l d m))
  needs-store {X} {e} {a} {k} c with needs-putTx {X} {e} {a} {k} c
  ... | l , d , refl = l , d , stPutTx , refl

  -- THE SHARED LEAVES: the vacuous-leaf lemmas at both carriers, the two guarantee
  -- alphabets and their `Sep`s, and the prototype peer bundle.  RE-EXPORTED, so that
  -- `Leios.TxSystemL` reaches them through this module instead of re-applying
  -- `OriginLeaves.Generic.Leaves` at the same eleven arguments.
  open OL.Generic.Leaves p t apiES Minted TxKey txCarries txWA txNext
                         _⊆_ ⊆-refl ⊆-trans txNext-⊆ needs-store public

  -- the assume-guarantee carrier at the S5 discipline … also re-exported, so that the
  -- `Wf` a system module folds with is THIS module application's and not a second one
  open BP.Carrier (Net_Api-≟ {Payload}) Minted TxKey txCarries txWA
                  txNext _⊆_ ⊆-trans txNext-⊆
    using ( OK; lbl; Wf; nowW; stepW; wf-mono; wf-mono-G; wf-Skip; wf-deadlock
          ; Sep; _∪α_; wf-Par; wf-⦀; wf-⦀⋆
          -- … and the four only a SYSTEM fold needs
          ; wf-⦀Fin⁺; HideCov; HideKeep; wf-Hide ) public

  -- … and its returning-tree layer, at the SAME arguments, so the two `Wf`s are the
  -- same record
  open BPW.Body (Net_Api-≟ {Payload}) Minted TxKey txCarries txWA
                txNext _⊆_ ⊆-refl ⊆-trans txNext-⊆
    using ( WfR; nowR; stepR; retR; Stable; stable-node; stable-□
          ; wfR-mono; wfR-Ret; wfR-Stop; wfR-Prefix; wfR-Output; wfR-⊓; wfR-□
          ; wfR->>=; wf-loop; wf-loop0; wf-⦀⁺; wf-⦀⁺∈ )

  ------------------------------------------------------------------------
  -- THE BRIDGE
  ------------------------------------------------------------------------

  -- `OK` at a mempool deposit IS the gate, and at every other channel the gate is `true`
  gate-ok-aux : (ms : Minted) (z : Maybe ((Link × Dir) × Tx))
              → (∀ {k} → maybe′ (λ y → carriesAt y k) ⊥ z → memKey k ms ≡ true)
              → maybe′ (vouched ms) true z ≡ true
  gate-ok-aux ms nothing           g = refl
  gate-ok-aux ms (just (ld , tx′)) g = g refl

  -- `OK` at a label IS the gate
  ok→gate : ∀ {X} {e : Net_Api Payload X} {a : X} {ms}
          → (∀ {k} → txCarries (X , e) a k → txWA ms k)
          → txGate ms (X , e) a ≡ true
  ok→gate {X} {e} {a} {ms} f = gate-ok-aux ms (isPutTx (X , e) a) f

  -- A `Wf` FACT ON THE FULL ALPHABET IS AN `OSafe` FACT.  The two carriers agree by
  -- construction: `txNext` on a visible label IS `mintedAfter`, `OK` at a label IS the
  -- gate (`ok→gate`), and `Wf` on `fullα` guarantees it for every label.  `OSafe`'s
  -- `noTick` comes from `NoRet`, which belongs to the COMPOSITE, not to the peer bundle,
  -- which does return.
  wf→osafe : ∀ {ms} {M : Proc} → Wf fullα ms M → NoRet M → OSafe ms M
  wf→osafe {ms = ms} w nr .gateOK {X} {e} {a} st =
    ok→gate {X} {e} {a} {ms} (nowW w ⊆-refl tt st)
  wf→osafe w nr .onτ    st = wf→osafe (stepW w ⊆-refl st tt) (NoRet.stepNR nr st)
  wf→osafe w nr .onEv   st =
    wf→osafe (stepW w ⊆-refl st (nowW w ⊆-refl tt st)) (NoRet.stepNR nr st)
  wf→osafe w nr .noTick st = noRet→noTick nr st

  -- a membership fact transported along a proved hash equality.  `putChecked`'s guard
  -- proves `txHash tx ≡ k`; the mint is about `k`; this is the one step between.
  mem-≡ : ∀ (ld : Link × Dir) (h h′ : TxHash) (ms : Minted) → h ≡ h′
        → memKey (ld , h′) ms ≡ true → memKey (ld , h) ms ≡ true
  mem-≡ ld h .h ms refl m = m

  ------------------------------------------------------------------------
  -- THE `noTxPut` BLOCK — S5's own vacuity alphabet
  --
  -- `BodyOrigin.noPuts` excludes `stPut`/`stPutBody` (for S1 and S4) and does NOT
  -- cover `stPutTx`, so S5 cannot borrow it.  This is the analogue, and it is a
  -- one-tag alphabet because S5 gates exactly one channel.
  ------------------------------------------------------------------------

  -- A CHANNEL THAT IS NOT THE MEMPOOL DEPOSIT.  A thread confined to this alphabet is
  -- vacuous for S5 and its leaf costs one line.
  noTxPut : Alpha
  noTxPut (_ , store _ _ stPutTx) _ = ⊥
  noTxPut _                       _ = ⊤ {0ℓ}

  -- … hence S5's own vacuity: everything S5's `Carries` speaks about is a `stPutTx`,
  -- which `noTxPut` excludes
  nTP→noNeed : ∀ at a → noTxPut at a → noNeed at a
  nTP→noNeed (X , e) a np {k} c with needs-putTx {X} {e} {a} {k} c
  ... | l , d , refl = np

  -- a thread confined to `noTxPut` carries nothing for S5 …
  oo↓ : ∀ {ℓr} {R : Set ℓr} {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
      → OffersOnly noTxPut M → OffersOnly noNeed M
  oo↓ = OffersOnly-mono nTP→noNeed

  -- … and is therefore a `Wf` leaf at every guarantee alphabet and every state
  wf-nP : ∀ {G ms} {M : Proc} → OffersOnly noTxPut M → Wf G ms M
  wf-nP oo = wf-free (oo↓ oo)

  ------------------------------------------------------------------------
  -- The thirteen threads (and five helpers) that never deposit a transaction
  --
  -- Each is a `loop`/`loop0` over a chain of prefixes and outputs on channels other
  -- than `store … stPutTx`, so `noTxPut` holds at every offer by reduction and the whole
  -- discharge is `OffersOnly-Prefix`/`-Output`/`->>=` plumbing.  TWO of them —
  -- `forgeL` and `fetchBody` — are CONTENT-BEARING for S1 and vacuous here, which is the
  -- mirror image of `BodyOrigin`'s tx-route leaves.
  ------------------------------------------------------------------------

  -- the certificate half of a forge pass: an `stHasCert` rendezvous and an RB deposit
  oo-forgeCertL : ∀ n b → OffersOnly noTxPut (forgeCertL n b)
  oo-forgeCertL n b with rbCert b
  ... | nothing = OffersOnly-Skip
  ... | just r  = OffersOnly-Prefix₀ (λ _ → tt) (OffersOnly-Output tt OffersOnly-Skip)

  -- one forge pass: an EB-BODY deposit and the certificate half, never a transaction
  oo-forgeBodyL : ∀ n mb → OffersOnly noTxPut (forgeBodyL n mb)
  oo-forgeBodyL n (nothing , b) with forgeOK (nothing , b)
  ... | true  = oo-forgeCertL n b
  ... | false = OffersOnly-Skip
  oo-forgeBodyL n (just eb , b) with forgeOK (just eb , b)
  ... | true  = OffersOnly-Output tt (oo-forgeCertL n b)
  ... | false = OffersOnly-Skip

  -- THE FORGE THREAD, vacuous for S5: it deposits an EB body and a ranking block
  oo-forgeL : ∀ n → OffersOnly noTxPut (forgeL n)
  oo-forgeL n = OffersOnly-loop0 (OffersOnly-Prefix (λ _ → tt) (oo-forgeBodyL n))

  -- the EB index: it reads held blocks and deposits EB ENTRIES (`stPutEB`)
  oo-ebIndex : ∀ n → OffersOnly noTxPut (ebIndex n)
  oo-ebIndex n = OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt) (body k))
    where
    -- one pass, once the k-th oldest held block is in hand
    body : ∀ k b → OffersOnly noTxPut
             (maybe′ (λ h → putEBEv n ! (h , slotOf b) ⟶ Ret (suc k))
                     (Ret (suc k)) (announcedEB b))
    body k b with announcedEB b
    ... | nothing = OffersOnly-Ret
    ... | just h  = OffersOnly-Output tt OffersOnly-Ret

  -- the voter: two store READS and a VOTE deposit (`stPutVote`)
  oo-voter : ∀ n → OffersOnly noTxPut (voter n)
  oo-voter n = OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt) (body k))
    where
    -- one pass, once the ranking block is in hand
    body : ∀ k b → OffersOnly noTxPut
             (maybe′ (λ h → getBodyEv n h ⟶ (λ _ →
                        putVoteEv n ! mkVoteBlob (voterOf n) (rbHash b) ⟶ Ret (suc k)))
                     (Ret (suc k)) (announcedEB b))
    body k b with announcedEB b
    ... | nothing = OffersOnly-Ret
    ... | just h  =
      OffersOnly-Prefix (λ _ → tt) (λ _ → OffersOnly-Output tt OffersOnly-Ret)

  -- the certificate sink: one `stCert` read per pass
  oo-certSink : ∀ n → OffersOnly noTxPut (certSink n)
  oo-certSink n = OffersOnly-loop0 (OffersOnly-Prefix (λ _ → tt) (λ _ → OffersOnly-Skip))

  -- the BlockFetch client thread: it deposits a BLOCK received off the wire (`stPut`)
  oo-clientLoop : ∀ n ld → OffersOnly noTxPut (clientLoop n ld)
  oo-clientLoop n (l , d) =
    OffersOnly-loop0 (OffersOnly-Prefix₀ (λ _ → tt) (OffersOnly-Prefix (λ _ → tt) k))
    where
    -- the reaction to one header: request the block, receive it, deposit it
    k : ∀ a → OffersOnly noTxPut (clientBody-k n l d a)
    k (header b , _) =
      OffersOnly-Output tt
        (OffersOnly-Prefix (λ _ → tt) (λ _ → OffersOnly-Output tt OffersOnly-Skip))

  -- one ChainSync server round, `NodeLogic.serverBody-k` verbatim: api events only
  oo-serverBody-k : ∀ n l d b → OffersOnly noTxPut (serverBody-k n l d b)
  oo-serverBody-k n l d b =
    OffersOnly-Prefix₀ (λ _ → tt)
      (OffersOnly-Output tt
        (OffersOnly-Prefix (λ _ → tt) (λ _ →
          OffersOnly-Prefix₀ (λ _ → tt)
            (OffersOnly-Output tt
              (OffersOnly-Prefix₀ (λ _ → tt) OffersOnly-Skip)))))

  -- the ChainSync server thread
  oo-serverLoopL : ∀ n ld → OffersOnly noTxPut (serverLoopL n ld)
  oo-serverLoopL n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix₀ (λ _ → tt)
      (OffersOnly-Prefix (λ _ → tt) (λ b →
        OffersOnly->>= (oo-serverBody-k n l (opposite d) b) (λ _ → OffersOnly-Ret))))

  -- the LN announce thread: a held-block read and an announcement
  oo-lnServerLoopL : ∀ n ld → OffersOnly noTxPut (lnServerLoopL n ld)
  oo-lnServerLoopL n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt)
                             (λ b → OffersOnly-Output tt OffersOnly-Ret))

  -- the tx-closure gate: mempool READS only (`stGetTx`), so it keeps any `noTxPut` continuation
  oo-awaitTxs : ∀ n (hs : List (TxHash × Size)) {P}
              → OffersOnly noTxPut P → OffersOnly noTxPut (awaitTxs n hs P)
  oo-awaitTxs n []             oo = oo
  oo-awaitTxs n ((h , _) ∷ hs) oo = OffersOnly-Prefix (λ _ → tt) (λ _ → oo-awaitTxs n hs oo)

  -- the body-offer thread: two store READS and two offers
  oo-bodyOfferLoop : ∀ n ld → OffersOnly noTxPut (bodyOfferLoop n ld)
  oo-bodyOfferLoop n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt) (body k))
    where
    -- one pass, once the k-th oldest held block is in hand
    body : ∀ k b → OffersOnly noTxPut
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
    ... | just h  = OffersOnly-Prefix (λ _ → tt) (λ eb →
                      OffersOnly-Output ⦃ DecEq-Offer ⦄ tt
                        (oo-awaitTxs n (ebTxs h)
                          (OffersOnly-Output ⦃ DecEq-EBPoint ⦄ tt OffersOnly-Ret)))

  -- the vote-offer thread: a vote-store read and a send
  oo-voteOfferLoop : ∀ n ld → OffersOnly noTxPut (voteOfferLoop n ld)
  oo-voteOfferLoop n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt)
                             (λ v → OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ tt
                                      OffersOnly-Ret))

  -- the EB-serve thread: it READS a body out of the store and sends it
  oo-ebServeLoop : ∀ n ld → OffersOnly noTxPut (ebServeLoop n ld)
  oo-ebServeLoop n (l , d) =
    OffersOnly-loop0 (OffersOnly-Prefix (λ _ → tt) (λ q →
      OffersOnly-Prefix (λ _ → tt) (λ eb → OffersOnly-Output tt OffersOnly-Skip)))

  -- the tx-closure server's reply builder: mempool READS and one send
  oo-serveTxs : ∀ n l d q bm acc → OffersOnly noTxPut (serveTxs n l d q bm acc)
  oo-serveTxs n l d q []       acc =
    OffersOnly-Output ⦃ DecEq-TxsReply ⦄ tt OffersOnly-Skip
  oo-serveTxs n l d q (o ∷ os) acc with at? o (ebTxs (proj₁ q))
  ... | nothing      = oo-serveTxs n l d q os acc
  ... | just (h , _) = OffersOnly-Prefix (λ _ → tt)
                         (λ tx′ → oo-serveTxs n l d q os (acc ++ ((o , tx′) ∷ [])))

  -- the tx-closure-serve thread
  oo-ebTxsServeLoop : ∀ n ld → OffersOnly noTxPut (ebTxsServeLoop n ld)
  oo-ebTxsServeLoop n (l , d) =
    OffersOnly-loop0 (OffersOnly-Prefix (λ _ → tt) (λ { (q , bm) →
      OffersOnly-Prefix (λ _ → tt) (λ _ → oo-serveTxs n l (opposite d) q bm []) }))

  -- the TxSubmission serve thread: a mempool read and two replies
  oo-tsServe : ∀ n ld → OffersOnly noTxPut (tsServe n ld)
  oo-tsServe n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt) (λ _ →
      OffersOnly-Prefix (λ _ → tt) (λ tx′ →
        OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ tt
          (OffersOnly-Prefix (λ _ → tt) (λ _ →
            OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ tt OffersOnly-Ret)))))

  -- fetch an offered EB BODY: it deposits a body, which S5 does not gate.  (The mirror
  -- of `BodyOrigin`: content-bearing there, vacuous here.)
  oo-fetchBody : ∀ n l d qs → OffersOnly noTxPut (fetchBody n l d qs)
  oo-fetchBody n l d (q , sz) =
    OffersOnly-Output ⦃ DecEq-EBPoint ⦄ tt
      (OffersOnly-Prefix (λ _ → tt) (λ eb → guard eb))
    where
    -- the requested-point check around the body deposit
    guard : ∀ eb → OffersOnly noTxPut
              ((putBodyEv n ! eb ⟶ Skip {0ℓ}) ◁ ⌊ ebHash eb ≟ proj₁ q ⌋ ▷ Skip {0ℓ})
    guard eb with ⌊ ebHash eb ≟ proj₁ q ⌋
    ... | true  = OffersOnly-Output tt OffersOnly-Skip
    ... | false = OffersOnly-Skip

  -- every delivered vote blob, deposited in the VOTE store
  oo-putAllVotes : ∀ n vs → OffersOnly noTxPut (putAllVotes n vs)
  oo-putAllVotes n []       = OffersOnly-Skip
  oo-putAllVotes n (v ∷ vs) = OffersOnly-Output tt (oo-putAllVotes n vs)

  ------------------------------------------------------------------------
  -- THE THREE CONTENT-BEARING LEAVES
  --
  -- The only three threads that ever deposit a transaction.  Each reaches its deposit
  -- through a chain whose EARLIER step minted the very hash the deposit needs — a gate
  -- that opens in the middle of a loop body, which is what `wfR-Prefix`/`wfR-Output`/
  -- `wf-loop` are for and what a state-independent alphabet cannot express.
  ------------------------------------------------------------------------

  -- THE SUBMISSION THREAD.  The `env … envSubmit` rendezvous MINTS the hash of the very
  -- transaction it hands over, and the next step deposits that transaction.  The mint and
  -- the deposit both fire at `homeOf n`, so record η closes the endpoint bookkeeping
  -- definitionally — no `endpoints-sound` on this branch.  THE CLAUSE IS NOT DROPPABLE:
  -- all three routes share the `stPutTx` channel and the gate is per-channel.
  wf-submit : ∀ {ms} n → Wf fullα ms (submit n)
  wf-submit n = wf-loop0 (wfR-Prefix (λ _ _ _ → λ ()) (λ _ tx′ _ → dep tx′))
    where
    -- the deposit, at the state the submission event led to: that state's HEAD is the
    -- very key the deposit needs
    dep : ∀ {s} (tx′ : Tx)
        → WfR fullα (((homeOf n , txHash tx′)) ∷ s) (λ _ _ → ⊤ {0ℓ})
            (putTxEv n ! tx′ ⟶ Skip {0ℓ})
    dep {s} tx′ =
      wfR-Output (λ le _ → λ { refl →
                    memKey-mono le
                      (∈→memKey (homeOf n , txHash tx′)
                                ((homeOf n , txHash tx′) ∷ s) (here refl)) })
                 (λ _ _ → wfR-free OffersOnly-Skip tt)

  -- THE TXSUBMISSION PULL THREAD.  Its deposits are inside `putAllTx`, under the guard
  -- `memberOf (txHash tx) ids` against the id list THIS THREAD sent on
  -- `sendTSRequestTxsPipelined` — the step that MINTED those ids.  THAT GUARD IS THE
  -- CONTENT: an arbitrary delivered transaction's hash need not be in `ids`, so without
  -- it the leaf below has nothing to spend.  IT TAKES THE ENDPOINT'S MEMBERSHIP: the
  -- request mints at `homeOpp (l , opposite d)` and the deposit it licenses is at
  -- `homeOf n`, so the leaf has to know that `(l , d)` really is one of `n`'s endpoints.
  wf-tsPull : ∀ {ms} n ld → ld ∈ endpointsList n → Wf fullα ms (tsPull n ld)
  wf-tsPull n (l , d) mem =
    wf-loop0 (wfR-Output ⦃ DecEq-ℕ×ℕ ⦄ (λ _ _ → λ ()) (λ _ _ →
      wfR-Prefix (λ _ _ _ → λ ()) (λ _ ids _ →
        wfR-Output ⦃ DecEqI.DecEq-List ⦄ (λ _ _ → λ ()) (λ _ _ →
          wfR-Prefix (λ _ _ _ → λ ()) (λ le txs _ →
            deps ids txs (λ h q → start ids h le q))))))
    where
    -- A REQUEST AT THIS ENDPOINT MINTS AT THIS NODE'S OWN DEPOSIT ENDPOINT.  The mint is
    -- keyed by `homeOpp (l , opposite d)`, i.e. `homeOf (endAt l (opposite (opposite d)))`,
    -- and that node IS `n` because `(l , d)` is one of `n`'s endpoints — `sound-opp`,
    -- hence `Topology.endpoints-sound` through `opposite`'s involutivity.  THIS is the
    -- one leaf of the pull thread the threaded membership is spent at.
    start : ∀ {s′ s″ : Minted} (ids : List TxHash) (h : TxHash)
          → (map (λ h′ → (homeOpp (l , opposite d) , h′)) ids ++ s′) ⊆ s″
          → h ∈ ids → memKey (homeOf n , h) s″ ≡ true
    start {s″ = s″} ids h le q =
      ∈→memKey (homeOf n , h) s″
        (subst (λ z → (z , h) ∈ s″) (cong homeOf (sound-opp n l d mem))
          (le (∈-++⁺ˡ (∈-map⁺ (λ h′ → (homeOpp (l , opposite d) , h′)) q))))

    -- every REQUESTED transaction of the reply, deposited; an unrequested one is skipped.
    -- The guard's witness turns the deposit's obligation into the request's mint.
    deps : ∀ {s} (ids : List TxHash) (txs : List Tx)
         → (∀ h → h ∈ ids → memKey (homeOf n , h) s ≡ true)
         → WfR fullα s (λ _ _ → ⊤ {0ℓ}) (putAllTx n ids txs)
    deps ids []          hyp = wfR-free OffersOnly-Skip tt
    deps ids (tx′ ∷ txs) hyp with memberOfNL (txHash tx′) ids in eqm
    ... | true  =
      wfR-Output (λ le _ → λ { refl →
                    memKey-mono le (hyp (txHash tx′) (memNL→∈ (txHash tx′) ids eqm)) })
                 (λ le _ → deps ids txs (λ h q → memKey-mono le (hyp h q)))
    ... | false = deps ids txs hyp

  -- THE NOTIFY CLIENT.  Its mempool deposits are inside `fetchTxs`, under the guard
  -- `⌊ txHash tx ≟ k ⌋` with `k` read out of `at? o (ebTxs h)` for the point `h` this
  -- very thread requested on `lfpSendBlockTxsRequest` — the step that MINTED every hash
  -- that table names.  THAT GUARD IS THE CONTENT: without it an entry may carry any
  -- transaction at all.  The other three branches deposit an EB BODY, nothing, and VOTE
  -- BLOBS respectively, none of which S5 gates.
  wf-lnClient : ∀ {ms} n ld → ld ∈ endpointsList n → Wf fullα ms (lnClientLoopL n ld)
  wf-lnClient n (l , d) mem = wf-loop0 (wfR-Prefix (λ _ _ _ → λ ()) (λ _ _ _ → choice))
    where
    -- the announcement branch: a no-op
    annB : ∀ {s} → WfR fullα s (λ _ _ → ⊤ {0ℓ})
             (apiLP l d lnpRecvBlockAnnouncement ⟶ (λ _ → Skip))
    annB = wfR-free (OffersOnly-Prefix (λ _ → λ ()) (λ _ → OffersOnly-Skip)) tt

    -- the body-offer branch: an EB body, not a transaction
    offB : ∀ {s} → WfR fullα s (λ _ _ → ⊤ {0ℓ})
             (apiLP l d lnpRecvBlockOffer ⟶ fetchBody n l d)
    offB = wfR-free (OffersOnly-Prefix (λ _ → λ ())
                      (λ qs → oo↓ (oo-fetchBody n l d qs))) tt

    -- the votes branch: vote blobs, not transactions
    votB : ∀ {s} → WfR fullα s (λ _ _ → ⊤ {0ℓ}) (apiLP l d lnpRecvVotes ⟶ putAllVotes n)
    votB = wfR-free (OffersOnly-Prefix (λ _ → λ ())
                      (λ vs → oo↓ (oo-putAllVotes n vs))) tt

    -- A TX-CLOSURE REQUEST AT THIS ENDPOINT MINTS AT THIS NODE'S OWN DEPOSIT ENDPOINT,
    -- one key per entry of the requested point's EB body table.  `homeAt (l , d)` is
    -- `homeOf (endAt l d)` and `endAt l d` IS `n` — `Topology.endpoints-sound`, through
    -- `sound-at`.  THIS is the one leaf of the Notify client the membership is spent at.
    atHome : ∀ {s′ s″ : Minted} (q : EBHash × LSlot)
           → (tableKeys (homeAt (l , d)) (proj₁ q) ++ s′) ⊆ s″
           → ∀ {k : TxHash} {sz : Size} → (k , sz) ∈ ebTxs (proj₁ q)
           → memKey (homeOf n , k) s″ ≡ true
    atHome {s″ = s″} q le {k} q∈ =
      ∈→memKey (homeOf n , k) s″
        (subst (λ z → (z , k) ∈ s″) (cong homeOf (sound-at n l d mem))
          (le (∈-++⁺ˡ (∈-map⁺ (λ e → (homeAt (l , d) , proj₁ e)) q∈))))

    -- THE GUARDED DEPOSITS: an entry `(o , tx)` is stored only when `tx` hashes to what
    -- the table names at offset `o`, and every hash that table names is minted by the
    -- premise.  The `with` mirrors `putChecked`'s own, with `in` so the offset lookup's
    -- equation survives into `at?-∈`.
    dep : ∀ {s} (h : EBHash) (es : List (ℕ × Tx))
        → (∀ {k : TxHash} {sz : Size} → (k , sz) ∈ ebTxs h → memKey (homeOf n , k) s ≡ true)
        → WfR fullα s (λ _ _ → ⊤ {0ℓ}) (putChecked n h es)
    dep h []              hyp = wfR-free OffersOnly-Skip tt
    dep h ((o , tx′) ∷ es) hyp with at? o (ebTxs h) in eqa
    ... | nothing = dep h es hyp
    ... | just (k , sz) with txHash tx′ ≟ k
    ...   | no  _  = dep h es hyp
    ...   | yes pr =
      wfR-Output (λ {s′} le _ → λ { refl →
                    mem-≡ (homeOf n) (txHash tx′) k s′ pr
                      (memKey-mono le (hyp (at?-∈ o (ebTxs h) eqa))) })
                 (λ le _ → dep h es (λ q → memKey-mono le (hyp q)))

    -- the echoed-point check around the deposits
    guard : ∀ {s} (q q′ : EBHash × LSlot) (es : List (ℕ × Tx))
          → (∀ {k : TxHash} {sz : Size} → (k , sz) ∈ ebTxs (proj₁ q)
             → memKey (homeOf n , k) s ≡ true)
          → WfR fullα s (λ _ _ → ⊤ {0ℓ})
              (putChecked n (proj₁ q) es ◁ ⌊ DecEq-EBPoint ._≟_ q′ q ⌋ ▷ Skip {0ℓ})
    guard q q′ es hyp with ⌊ DecEq-EBPoint ._≟_ q′ q ⌋
    ... | true  = dep (proj₁ q) es hyp
    ... | false = wfR-free OffersOnly-Skip tt

    -- the reaction to one tx-closure offer: block at the body, REQUEST every offset —
    -- which MINTS every hash the table names — take the reply, and deposit the checked
    -- entries
    fetch : ∀ {s} (q : EBHash × LSlot) → WfR fullα s (λ _ _ → ⊤ {0ℓ}) (fetchTxs n l d q)
    fetch q =
      wfR-Prefix (λ _ _ _ → λ ()) (λ _ _ _ →
        wfR-Output ⦃ DecEq-TxsRequest ⦄ (λ _ _ → λ ()) (λ _ _ →
          wfR-Prefix (λ _ _ _ → λ ())
            (λ le → λ { (q′ , es) _ → guard q q′ es (atHome q le) })))

    -- the tx-closure branch: THE CONTENT-BEARING one
    txB : ∀ {s} → WfR fullα s (λ _ _ → ⊤ {0ℓ})
            (apiLP l d lnpRecvBlockTxsOffer ⟶ fetchTxs n l d)
    txB = wfR-Prefix (λ _ _ _ → λ ()) (λ _ q _ → fetch q)

    -- the four branches, offered together
    choice : ∀ {s} → WfR fullα s (λ _ _ → ⊤ {0ℓ})
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

  -- one endpoint's ten threads.  EIGHT of them carry nothing and ignore the membership;
  -- the Notify client and the TxSubmission pull thread each spend it.
  wf-endpoint : ∀ {ms} n e → e ∈ endpointsList n → Wf fullα ms (endpointThreadsL n e)
  wf-endpoint n e mem =
    wf-⦀ (wf-nP (oo-clientLoop n e))
      (wf-⦀ (wf-nP (oo-serverLoopL n e))
      (wf-⦀ (wf-lnClient n e mem)
      (wf-⦀ (wf-nP (oo-lnServerLoopL n e))
      (wf-⦀ (wf-nP (oo-bodyOfferLoop n e))
      (wf-⦀ (wf-nP (oo-voteOfferLoop n e))
      (wf-⦀ (wf-nP (oo-ebServeLoop n e))
      (wf-⦀ (wf-nP (oo-ebTxsServeLoop n e))
      (wf-⦀ (wf-tsPull n e mem) (wf-nP (oo-tsServe n e))))))))))

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
    wf-⦀ (wf-nP (oo-forgeL n))
      (wf-⦀ (wf-nP (oo-ebIndex n))
      (wf-⦀ (wf-nP (oo-voter n))
      (wf-⦀ (wf-submit n)
      (wf-⦀ (wf-nP (oo-certSink n)) (wf-allThreads n)))))

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

  -- S5 — TRANSACTION ORIGIN, node-local.  A node running `nodeLogicL` from empty stores
  -- puts no transaction in its mempool that it was neither handed nor asked for AT ONE
  -- OF ITS OWN ENDPOINTS.  LEVEL: node — `Leios.TxSystemL` lifts this to the whole
  -- network.  See the module header for the two honest limits and for the full list of
  -- what this does not rule out; in particular it is a DIFFUSION-HYGIENE statement, and
  -- no transaction in this model ever reaches consensus.
  TxSound : Set₁
  TxSound = ∀ (n : Node) → TxSpecT ⊑T nodeP n (nodeLogicL n st₀)

  -- S5 FOR ANY LOGIC THAT CARRIES THE GATE AND NEVER RETURNS, INSIDE THE BUNDLE.  The
  -- bundle and the logic compose on `apiES` at the full guarantee alphabet (`Sep apiES`
  -- is trivial there), and `wf→osafe` then `osafe→⊑T` turn that one `Wf` fact into the
  -- trace refinement.
  soundOf : ∀ n (lg : Proc) → Wf fullα [] lg → NoRet lg → TxSpecT ⊑T nodeP n lg
  soundOf n lg w nr =
    osafe→⊑T (wf→osafe (wf-mono-G (λ _ _ _ → inj₁ tt)
                         (wf-Par apiES sep-api (wf-linkBundlesP n) w))
                       (NoRet-ParR apiES nr))

  -- … and the same WITHOUT the peer bundle, for a composite stated at the node logic
  -- alone.  This is the load-bearing half of `soundOf`: the bundle contributes only
  -- `wf-linkBundlesP`, which is vacuous (no peer offers a `store` channel).
  soundLogic : ∀ (lg : Proc) → Wf fullα [] lg → NoRet lg → TxSpecT ⊑T lg
  soundLogic lg w nr = osafe→⊑T (wf→osafe w nr)

  -- S5, PROVED, at the shipped node logic from empty stores
  txSound : TxSound
  txSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)

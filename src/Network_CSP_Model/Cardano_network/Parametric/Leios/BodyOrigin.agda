{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S1, BODY ORIGIN: a node stores an EB body only
-- if it FORGED that body or ASKED FOR the point the body matches.
--
-- WHAT S1 SAYS.  A node running `nodeLogicL` from empty stores performs
-- `store home(n) stPutBody ! eb` only when `ebHash eb` is
--
--   * the hash of an EB the environment handed it at `env … envForge`
--     — the node forged a body with that hash; or
--   * the hash inside a point the node ITSELF put on the wire at
--     `apiLP l d lfpSendBlockRequest` — the node stored a body whose hash
--     is the point it requested.
--
-- IN ONE SENTENCE, AND THIS IS THE QUOTABLE FORM: node `n`, running the full
-- real `nodeLogicL` from empty stores inside its prototype peer bundle,
-- never performs `store home(n) stPutBody ! eb` unless an earlier event of
-- the same trace was an `env … envForge` carrying an EB with that hash or an
-- `apiLP … lfpSendBlockRequest` for a point with that hash — saying nothing
-- about whether the request was wise, whether a hash-colliding body was
-- substituted, how long or how often one request keeps licensing deposits,
-- or about any other store.
--
-- THE WIRE GUARD IS WHAT MAKES THE SECOND CASE TRUE.  The prototype's
-- `MsgLeiosBlock` carries NO point (spec §2.2), so a delivered body cannot
-- be keyed by anything the wire says: `NodeLogicL.fetchBody` keys it against
-- `proj₁ q`, the point the client sent one step earlier, with
-- `⌊ ebHash eb ≟ proj₁ q ⌋`.  That guard is this theorem's whole content and
-- it is exactly what the negative control (`BodyOriginBad`) deletes.
--
-- WHAT S1 DOES **NOT** RULE OUT — READ BEFORE QUOTING IT.
--   * It says nothing about whether the body the node asked for is the body
--     it should have asked for: any point that reaches the Notify client in
--     an OFFER may be requested, and a request MINTS.  S1 is a
--     "no unsolicited bodies" statement, not a validity statement — the
--     prototype has no notion of a valid EB body at all.
--   * `ebHash` IS NOWHERE ASSUMED INJECTIVE, so the guard fixes the HASH and
--     not the CONTENT: a peer that answers the request with different
--     content colliding on `proj₁ q` passes `⌊ ebHash eb ≟ proj₁ q ⌋` and
--     its body is stored.  What S1 buys is exactly "the stored body's hash
--     is the point this node sent", never "the stored body is the one the
--     honest producer holds at that point".
--   * THE MINTED SET IS APPEND-ONLY AND UNPAIRED (`mintedAfter at a ms =
--     mints at a ++ ms`): a permission, once granted, is permanent and is
--     never consumed by the deposit that spends it.  So ONE
--     `lfpSendBlockRequest` licenses UNBOUNDEDLY MANY later deposits of that
--     hash, at any endpoint and at any later time.  S1 is "every deposit has
--     an earlier origin", not "one request, one deposit".
--   * A FORGE THE BLOCK STORE REJECTS STILL MINTS: `bodyMints` fires on the
--     `env … envForge` LABEL, whereas `forgeBodyL` suppresses the deposit
--     under `forgeOK` — so the permission outlives the rejection.  (This is
--     a weakening of the gate, never of soundness: the deposit it licenses is
--     one `forgeBodyL` does not make.)
--   * It says nothing about the BLOCK store (`stPut`), the mempool
--     (`stPutTx`), the EB-entry store (`stPutEB`) or the vote store
--     (`stPutVote`).  `storeStepL`'s `putEv` branch is deliberately ungated
--     (see `NodeLogicL`'s S4 scope note) and the tx-closure branch deposits
--     transactions under its own check; neither is S1's business.
--   * It says nothing about OTHER nodes: it is a NODE-level statement about
--     one node's own logic inside its own peer bundle (see the caveat
--     below), not a network-wide "every body held anywhere was forged
--     somewhere".
--   * It is purely safety-shaped.  No module here exhibits a good node
--     actually reaching `stPutBody`; the three liveness ceilings recorded in
--     Task 4 are untouched.
--
-- THE DISCIPLINE IS ENDPOINT-INDEXED, AND THAT IS WHAT LETS IT LIFT.  The key
-- is an EB hash TOGETHER WITH THE DEPOSIT ENDPOINT it licenses
-- (`BodyKey = (Link × Dir) × EBHash`, so `Minted = List BodyKey`).  An
-- `env l d envForge` carrying `e` mints `((l , d) , ebHash e)` — node-local,
-- since `forgeEv n` fires at `homeOf n`, which is also where `putBodyEv n`
-- fires, so record η closes that half definitionally.  An
-- `apiLP l d lfpSendBlockRequest ! q` mints `(homeAt (l , d) , proj₁ q)`,
-- where `homeAt (l , d)` is the home endpoint of the node that OWNS
-- `(l , d)`; a `store l d stPutBody ! eb` demands `((l , d) , ebHash eb)`.
-- Since `homeOf` is injective (`homeOf-inj`), a request sent at node X mints
-- no key any deposit of node Y can spend, and `Leios.BodySystemL` spends
-- exactly that.  The request mint has to be NORMALISED to the depositing
-- endpoint rather than keyed by the sending one, because a node sends at
-- every incident endpoint but deposits only at `homeOf n`; the normalisation
-- is sound because `Topology.endpoints-sound` identifies the owner of
-- `(l , d)`, which the membership-carrying fold
-- `BlockProvenanceWfR.wf-⦀⁺∈` delivers to the one leaf that needs it.
--
-- THE RE-KEYED NODE-LEVEL THEOREM IS **NO WEAKER** THAN THE OLD ONE, and that
-- is the direction that may be quoted.  Whenever the new gate stands open at
-- a deposit, so did the old one: the new minted set holds
-- `((l , d) , ebHash eb)`, which only a forge of that hash or a request for
-- that point can have put there — so the old endpoint-blind
-- `memberOf (ebHash eb)` was `true` too.  Hence every trace the NEW
-- `BodySpecT` permits the old one permitted.  The converse is NOT proved
-- here, so "no weaker" is the claim, never "strictly stronger".
--
-- HOW IT IS PROVED.  The assume-guarantee route S2/S2′ take —
-- `BlockProvenance.Carrier` plus `BlockProvenanceWfR.Body`, the shared
-- leaves of `OriginLeaves`, and `wf→osafe` back into `OriginSafe`.  THE
-- GATED CHANNEL IS EMITTED BY A THREAD (`forgeL`'s `forgeBodyL` and the
-- Notify client's `fetchBody`), never by a store, so this is S2's
-- ORIENTATION and not S3's: the thread group carries `fullα`, the store
-- group `∅α`, the `Sep` is `sep-store`, and the assembly is
-- `wf-withStores`.
--
-- ============ THE `noPuts` BLOCK, AND WHY IT EXISTS (for S4) ============
--
-- Eighteen of the twenty leaves below are threads that carry nothing under
-- S1.  They are NOT written at S1's own `noNeed`: they are written at
-- `noPuts`, the alphabet "this channel is neither `stPut` nor `stPutBody`",
-- and S1 gets its own vacuity from them in one line (`oo↓`/`wf-nP`).
--
-- The point is S4 (spec §5.4), which gates `stPut`.  S2′ could transport its
-- vacuous leaves from S2 because S2′'s `Carries` is contained in S2's; S4
-- CANNOT transport from S2 (S2 does not gate `stPut`, so the implication
-- runs the wrong way) and cannot transport from S1 either, for the same
-- reason in the other direction.  What S4 CAN do is take the `noPuts` block
-- verbatim: `noPuts` excludes BOTH thread-emitted deposits, so every thread
-- proved vacuous here is vacuous for S4 too, and S4's own
-- `noPuts → noNeed` is the same three lines as `nP→noNeed` below with its
-- own `needs-*`.  What S4 must still write for itself are the THREE leaves
-- that fall outside `noPuts`: `oo-clientLoop` (written here at S1's
-- `noNeed`, because it offers `stPut`, which is precisely what S4 gates) and
-- vacuity for `lnClientLoopL` (content-bearing here, vacuous there — the
-- shapes are `oo-fetchBody` / `oo-fetchDep`).  `forgeL` is content-bearing
-- for BOTH, because it deposits the EB body AND, after the `stHasCert`
-- rendezvous, a certificate-carrying ranking block; each theorem writes its
-- own `wf-forgeL`.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.BodyOrigin where

open import Level using (Level; 0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
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

-- the S1 origin discipline, parametric in the network parameters, the Leios
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
          ; lfpRecvBlock; lfpRecvBlockTxs; lfpReqBlockRequest; lfpReqBlockTxsRequest )
  -- `Tx`/`TxHash` come from `Params`; `DecEq-Tx` is deliberately NOT opened from `Data`,
  -- so `decTx` is the ONE `DecEq Tx` in scope and instance search resolves exactly the
  -- term `NodeLogicL` used (ledger gotcha 4).  Same for `decEBHash` and `DecEq EBHash`,
  -- which is what `fetchBody`'s wire guard decides on.
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
  open OS using (memberOf; memberOf-mono; ∈→memberOf)
  open OS.Generic p t apiES using (noRet→noTick)
  -- the PROTOTYPE peer bundle, whose nine `Wf` facts live in `OriginLeaves.Leaves`
  open import Cardano_network.Parametric.Leios.PeersP p using (nodeBundleP)

  instance
    -- product `DecEq` for the `sendCSRollForward` carrier (`Header × Tip`) — the same
    -- instance `NodeLogic` declares, so `OffersOnly-Output` sees the one the `!`-output
    -- in `serverBody-k` was built with (`VoteSound` does the same)
    DecEq-Header×Tip : DecEq (Header × Tip)
    DecEq-Header×Tip = DecEqI.DecEq-×

  ------------------------------------------------------------------------
  -- THE MINTED KEY, AND THE ENDPOINT BOOKKEEPING IT NEEDS
  ------------------------------------------------------------------------

  -- the endpoint equality, assembled out of the QUALIFIED `Fin` and `Dir` instances.
  -- Deliberately not an instance declaration: a product instance at this type would
  -- compete with the ones `wfR-Output` resolves its `DecEq X` to (campaign ledger,
  -- gotcha 4).  `CertSound.ld-≟` is the precedent.
  ld-≟ : (x y : Link × Dir) → Dec (x ≡ y)
  ld-≟ = ≡-dec (DecEq._≟_ DecEqI.DecEq-Fin) (DecEq._≟_ DecEq-Dir)

  -- THE MINTED KEY: AN EB HASH TOGETHER WITH THE DEPOSIT ENDPOINT IT LICENSES.  The
  -- endpoint index is what makes the discipline sound at a composite of SEVERAL nodes:
  -- without it a request sent at node X would licence a body deposit at node Y.
  BodyKey : Set
  BodyKey = (Link × Dir) × EBHash

  -- the key's equality, likewise explicit rather than an instance
  decBodyKey : DecEq BodyKey
  decBodyKey = record { _≟_ = ≡-dec ld-≟ (DecEq._≟_ decEBHash) }

  -- is this key in the minted set?  `OriginSafe.memberOf` at the equality above, passed
  -- explicitly because `memberOf` takes its `DecEq` as an INSTANCE argument and
  -- `decBodyKey` is not one
  memKey : BodyKey → List BodyKey → Bool
  memKey k ms = memberOf ⦃ decBodyKey ⦄ k ms

  -- … monotone in the minted set, which is what keeps the gate monotone
  memKey-mono : ∀ {k ms ms′} → ms ⊆ ms′ → memKey k ms ≡ true → memKey k ms′ ≡ true
  memKey-mono sub eq = memberOf-mono ⦃ decBodyKey ⦄ sub eq

  -- … and implied by propositional membership
  ∈→memKey : ∀ k ms → k ∈ ms → memKey k ms ≡ true
  ∈→memKey k ms q = ∈→memberOf ⦃ decBodyKey ⦄ k ms q

  -- `endpoints-sound` with the direction SPLIT FIRST.  The record's derived `endAt` is an
  -- extended lambda, which only reduces at a CONCRETE direction, so the law's conclusion
  -- at an abstract `d` is a stuck term that does not unify with `endAtT l d`
  -- (`BlobOrigin.sound-at` and `Topology.agda:225-227` make exactly this move).
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

  -- THE DEPOSIT ENDPOINT A REQUEST SENT AT ONE ENDPOINT LICENSES: the home endpoint of
  -- the node that owns the sending endpoint.  A node sends at EVERY endpoint incident to
  -- it but deposits only at `homeOf n` (`NodeLogicL.putBodyEv`), so a mint keyed by the
  -- sending endpoint itself would licence nothing at a node of degree > 1.
  homeAt : Link × Dir → Link × Dir
  homeAt ld = homeOf (endAtT (proj₁ ld) (proj₂ ld))

  ------------------------------------------------------------------------
  -- The origin discipline
  ------------------------------------------------------------------------

  -- IS THIS THE BODY-DEPOSIT CHANNEL, and if so which body?  The ONE channel dispatch
  -- of the discipline: the gate and the carrying relation both route through it, so
  -- each is discharged by a two-clause case on this `Maybe` instead of a
  -- thirty-two-clause alphabet enumeration (`needs-putBody` still writes that
  -- enumeration once, because its conclusion is a Σ about the channel).  The ENDPOINT is
  -- kept, because the key the deposit demands is indexed by it.
  isPutBody : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Maybe ((Link × Dir) × LeiosEb)
  isPutBody (_ , store l d stPutBody) eb = just ((l , d) , eb)
  isPutBody _                         _  = nothing

  -- WHAT MINTS.  A forge CARRYING an EB mints that EB's hash — a forge with no EB mints
  -- nothing, which is what keeps the property refutable.  The mint is on the LABEL, so a
  -- forge the block store goes on to REJECT (`forgeOK` false, or a cert-carrying RB under
  -- `acceptForgeL`) mints all the same; see the header.  A block REQUEST mints the
  -- hash inside the point it asked for: having asked for `q`, the node may store the
  -- body that hashes to `proj₁ q`, and nothing else.  The REPLY (`lfpRecvBlock`) mints
  -- NOTHING — minting there would make the wire branch vacuous and delete the theorem.
  -- BOTH MINTS ARE KEYED BY THE DEPOSIT ENDPOINT THEY LICENSE.  The forge is node-local
  -- (`forgeEv n` fires at `homeOf n`, which is exactly where `putBodyEv n` fires), so its
  -- own `(l , d)` is already the right key.  The request is PER-ENDPOINT, so it is
  -- normalised through `homeAt`: having asked at one of its endpoints, a node may deposit
  -- at its own.  `homeOf` is injective (`homeOf-inj`), so node X's requests mint no key
  -- node Y's deposits can spend — which is what lifts S1 to a system.
  bodyMints : (at : AnyTypes (Net_Api Payload)) → proj₁ at → List BodyKey
  bodyMints (_ , env l d envForge) mb =
    maybe (λ e → ((l , d) , ebHash e) ∷ []) [] (proj₁ mb)
  bodyMints (_ , apiLP l d lfpSendBlockRequest) q = (homeAt (l , d) , proj₁ q) ∷ []
  bodyMints _                                   _ = []

  -- IS THIS DEPOSIT LICENSED?  The body's hash must have been forged or requested here,
  -- FOR THIS VERY DEPOSIT ENDPOINT.
  vouched : List BodyKey → (Link × Dir) × LeiosEb → Bool
  vouched ms (ld , eb) = memKey (ld , ebHash eb) ms

  -- WHAT IS GATED: only an EB-body deposit, and only by `vouched`.  Everything else
  -- is free — in particular every other store deposit (see the module header).
  bodyGate : List BodyKey → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool
  bodyGate ms at a = maybe′ (vouched ms) true (isPutBody at a)

  -- the gate's monotonicity, as a case on `isPutBody`'s answer alone: the only
  -- state-dependent test is `memKey`, which is monotone
  gate-mono-aux : ∀ {ms ms′} → ms ⊆ ms′ → (z : Maybe ((Link × Dir) × LeiosEb))
                → maybe′ (vouched ms) true z ≡ true
                → maybe′ (vouched ms′) true z ≡ true
  gate-mono-aux sub nothing          eq = refl
  gate-mono-aux sub (just (ld , eb)) eq = memKey-mono sub eq

  -- MINTING ONLY EVER OPENS THE GATE
  bodyGate-mono : ∀ {ms ms′} → ms ⊆ ms′
                → ∀ at a → bodyGate ms at a ≡ true → bodyGate ms′ at a ≡ true
  bodyGate-mono sub at a eq = gate-mono-aux sub (isPutBody at a) eq

  ------------------------------------------------------------------------
  -- The specification S1 names
  ------------------------------------------------------------------------

  -- the generic carrier at the S1 discipline.  `OriginSpecT` is renamed rather than
  -- listed: Agda rejects a name that appears in both `using` and `renaming`.
  open OS.Generic.Origin p t apiES BodyKey decBodyKey bodyMints bodyGate bodyGate-mono
    using ( Minted; mintedAfter; mintedAfter-⊇; originOffer; OriginSpecAt; specAt-init
          ; OSafe; gateOK; onτ; onEv; noTick; osafe→⊑T )
    renaming (OriginSpecT to BodySpecT)
    public

  ------------------------------------------------------------------------
  -- The assume-guarantee instance, and the ONE alphabet enumeration
  ------------------------------------------------------------------------

  -- WHAT A DEPOSIT AT ONE ENDPOINT CARRIES: an obligation keyed by the body's hash AND
  -- the endpoint the deposit is made at
  carriesAt : (Link × Dir) × LeiosEb → BodyKey → Set
  carriesAt (ld , eb) k = (ld , ebHash eb) ≡ k

  -- WHAT A LABEL CARRIES: a body deposit carries the hash of the body it deposits KEYED
  -- BY THE ENDPOINT IT IS DEPOSITED AT; nothing else carries anything.  (This is the
  -- `Carries` of the Wf framework — "needs a justification" — NOT `bodyMints`.)
  bodyCarries : (at : AnyTypes (Net_Api Payload)) → proj₁ at → BodyKey → Set
  bodyCarries at a k = maybe′ (λ z → carriesAt z k) ⊥ (isPutBody at a)

  -- WHAT THE MINTED SET MUST SAY ABOUT A CARRIED KEY: that hash was forged or requested
  -- here, for that very deposit endpoint
  bodyWA : Minted → BodyKey → Set
  bodyWA ms k = memKey k ms ≡ true

  -- the state a label leads to: EXACTLY `OriginSafe`'s `mintedAfter` on a visible label
  -- (definitionally — `mintedAfter at a ms = mints at a ++ ms`), unchanged on τ and `√`
  bodyNext : Label (⊤ {0ℓ}) → Minted → Minted
  bodyNext (ev (evl (evLabel X e a))) ms = bodyMints (X , e) a ++ ms
  bodyNext _                          ms = ms

  -- the minted set only grows
  bodyNext-⊆ : ∀ a ms → ms ⊆ bodyNext a ms
  bodyNext-⊆ (ev (evl (evLabel X e a))) ms = mintedAfter-⊇ (X , e) a
  bodyNext-⊆ (ev (√ _))                 ms = λ q → q
  bodyNext-⊆ τ                          ms = λ q → q

  -- EVERY CARRYING CHANNEL IS THE BODY DEPOSIT.  One clause per `Net_Api` constructor
  -- and, under `store`, one per `StoreTag` — 32 clauses in all (18 non-`store`
  -- constructors plus 14 `StoreTag`s), of which 31 are absurd — because `isPutBody`'s catch-all
  -- does not reduce until the constructor is known.  This is the whole alphabet tax of
  -- S1, and it does double duty: `needs-store` and `nP→noNeed` both fall out of it.
  needs-putBody : ∀ {X} {e : Net_Api Payload X} {a : X} {k} → bodyCarries (X , e) a k
                → Σ[ l ∈ Link ] Σ[ d ∈ Dir ]
                    (_≡_ {A = AnyTypes (Net_Api Payload)}
                         (X , e) (StoreCar stPutBody , store l d stPutBody))
  needs-putBody {e = store l d stPutBody}       _  = l , d , refl
  needs-putBody {e = store _ _ stPut}           ()
  needs-putBody {e = store _ _ stGet}           ()
  needs-putBody {e = store _ _ (stGetAt _)}     ()
  needs-putBody {e = store _ _ stPutEB}         ()
  needs-putBody {e = store _ _ (stGetEBAt _)}   ()
  needs-putBody {e = store _ _ (stGetBody _)}   ()
  needs-putBody {e = store _ _ stPutTx}         ()
  needs-putBody {e = store _ _ (stGetTxAt _)}   ()
  needs-putBody {e = store _ _ stPutVote}       ()
  needs-putBody {e = store _ _ (stGetVoteAt _)} ()
  needs-putBody {e = store _ _ stCert}          ()
  needs-putBody {e = store _ _ (stGetTx _)}     ()
  needs-putBody {e = store _ _ (stHasCert _)}   ()
  needs-putBody {e = input _ _ _}               ()
  needs-putBody {e = output _ _ _}              ()
  needs-putBody {e = sndmsg _ _ _}              ()
  needs-putBody {e = rcvmsg _ _ _}              ()
  needs-putBody {e = tx _ _ _}                  ()
  needs-putBody {e = sndack _ _ _}              ()
  needs-putBody {e = rcvack _ _ _}              ()
  needs-putBody {e = ack _ _ _}                 ()
  needs-putBody {e = done _ _ _}                ()
  needs-putBody {e = apiCS _ _ _}               ()
  needs-putBody {e = apiBF _ _ _}               ()
  needs-putBody {e = apiTS _ _ _}               ()
  needs-putBody {e = apiKA _ _ _}               ()
  needs-putBody {e = apiLN _ _ _}               ()
  needs-putBody {e = apiLF _ _ _}               ()
  needs-putBody {e = apiLP _ _ _}               ()
  needs-putBody {e = env _ _ _}                 ()
  needs-putBody {e = break _}                   ()

  -- … weakened to the "some store tag" form `OriginLeaves` asks for
  needs-store : ∀ {X} {e : Net_Api Payload X} {a : X} {k} → bodyCarries (X , e) a k
              → Σ[ l ∈ Link ] Σ[ d ∈ Dir ] Σ[ m ∈ StoreTag ]
                  (_≡_ {A = AnyTypes (Net_Api Payload)}
                       (X , e) (StoreCar m , store l d m))
  needs-store {X} {e} {a} {k} c with needs-putBody {X} {e} {a} {k} c
  ... | l , d , refl = l , d , stPutBody , refl

  -- THE SHARED LEAVES: the vacuous-leaf lemmas at both carriers, the two guarantee
  -- alphabets and their `Sep`s, and the prototype peer bundle.  RE-EXPORTED, so that
  -- `Leios.BodySystemL` reaches them through this module instead of re-applying
  -- `OriginLeaves.Generic.Leaves` at the same eleven arguments.
  open OL.Generic.Leaves p t apiES Minted BodyKey bodyCarries bodyWA bodyNext
                         _⊆_ ⊆-refl ⊆-trans bodyNext-⊆ needs-store public

  -- the assume-guarantee carrier at the S1 discipline … also re-exported, so that the
  -- `Wf` a system module folds with is THIS module application's and not a second one
  open BP.Carrier (Net_Api-≟ {Payload}) Minted BodyKey bodyCarries bodyWA
                  bodyNext _⊆_ ⊆-trans bodyNext-⊆
    using ( OK; lbl; Wf; nowW; stepW; wf-mono; wf-mono-G; wf-Skip; wf-deadlock
          ; Sep; _∪α_; wf-Par; wf-⦀; wf-⦀⋆
          -- … and the four only a SYSTEM fold needs
          ; wf-⦀Fin⁺; HideCov; HideKeep; wf-Hide ) public

  -- … and its returning-tree layer, at the SAME arguments, so the two `Wf`s are the
  -- same record
  open BPW.Body (Net_Api-≟ {Payload}) Minted BodyKey bodyCarries bodyWA
                bodyNext _⊆_ ⊆-refl ⊆-trans bodyNext-⊆
    using ( WfR; nowR; stepR; retR; Stable; stable-node; stable-□
          ; wfR-mono; wfR-Ret; wfR-Stop; wfR-Prefix; wfR-Output; wfR-⊓; wfR-□
          ; wfR->>=; wf-loop; wf-loop0; wf-⦀⁺; wf-⦀⁺∈ )

  ------------------------------------------------------------------------
  -- THE BRIDGE
  ------------------------------------------------------------------------

  -- `OK` at a body deposit IS the gate, and at every other channel the gate is `true`
  gate-ok-aux : (ms : Minted) (z : Maybe ((Link × Dir) × LeiosEb))
              → (∀ {k} → maybe′ (λ y → carriesAt y k) ⊥ z → memKey k ms ≡ true)
              → maybe′ (vouched ms) true z ≡ true
  gate-ok-aux ms nothing          g = refl
  gate-ok-aux ms (just (ld , eb)) g = g refl

  -- `OK` at a label IS the gate
  ok→gate : ∀ {X} {e : Net_Api Payload X} {a : X} {ms}
          → (∀ {k} → bodyCarries (X , e) a k → bodyWA ms k)
          → bodyGate ms (X , e) a ≡ true
  ok→gate {X} {e} {a} {ms} f = gate-ok-aux ms (isPutBody (X , e) a) f

  -- A `Wf` FACT ON THE FULL ALPHABET IS AN `OSafe` FACT.  The two carriers agree by
  -- construction: `bodyNext` on a visible label IS `mintedAfter`, `OK` at a label IS
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

  -- a membership fact transported along a proved hash equality.  The wire guard proves
  -- `ebHash eb ≡ proj₁ q`; the mint is about `proj₁ q`; this is the one step between.
  mem-≡ : ∀ (ld : Link × Dir) (h h′ : EBHash) (ms : Minted) → h ≡ h′
        → memKey (ld , h′) ms ≡ true → memKey (ld , h) ms ≡ true
  mem-≡ ld h .h ms refl m = m

  ------------------------------------------------------------------------
  -- THE `noPuts` BLOCK — written for S4 as much as for S1 (module header)
  ------------------------------------------------------------------------

  -- A CHANNEL THAT IS NEITHER OF THE TWO THREAD-EMITTED STORE DEPOSITS.  `stPutBody` is
  -- what S1 gates and `stPut` is what S4 gates, so a thread confined to this alphabet is
  -- vacuous for BOTH theorems and its leaf is written exactly once, here.
  noPuts : Alpha
  noPuts (_ , store _ _ stPut)     _ = ⊥
  noPuts (_ , store _ _ stPutBody) _ = ⊥
  noPuts _                         _ = ⊤ {0ℓ}

  -- … hence S1's own vacuity: everything S1's `Carries` speaks about is a `stPutBody`,
  -- which `noPuts` excludes.  (S4's counterpart is these same three lines with its own
  -- `needs-*`; that is the whole cost of the transport.)
  nP→noNeed : ∀ at a → noPuts at a → noNeed at a
  nP→noNeed (X , e) a np {k} c with needs-putBody {X} {e} {a} {k} c
  ... | l , d , refl = np

  -- a thread confined to `noPuts` carries nothing for S1 …
  oo↓ : ∀ {ℓr} {R : Set ℓr} {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
      → OffersOnly noPuts M → OffersOnly noNeed M
  oo↓ = OffersOnly-mono nP→noNeed

  -- … and is therefore a `Wf` leaf at every guarantee alphabet and every state
  wf-nP : ∀ {G ms} {M : Proc} → OffersOnly noPuts M → Wf G ms M
  wf-nP oo = wf-free (oo↓ oo)

  ------------------------------------------------------------------------
  -- The twelve threads (and six helpers) that touch neither deposit
  --
  -- Each is a `loop`/`loop0` over a chain of prefixes and outputs on channels other
  -- than `store … stPut` and `store … stPutBody`, so `noPuts` holds at every offer by
  -- reduction and the whole discharge is `OffersOnly-Prefix`/`-Output`/`->>=` plumbing.
  ------------------------------------------------------------------------

  -- the EB index: it reads held blocks and deposits EB ENTRIES (`stPutEB`)
  oo-ebIndex : ∀ n → OffersOnly noPuts (ebIndex n)
  oo-ebIndex n = OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt) (body k))
    where
    -- one pass, once the k-th oldest held block is in hand
    body : ∀ k b → OffersOnly noPuts
             (maybe′ (λ h → putEBEv n ! (h , slotOf b) ⟶ Ret (suc k))
                     (Ret (suc k)) (announcedEB b))
    body k b with announcedEB b
    ... | nothing = OffersOnly-Ret
    ... | just h  = OffersOnly-Output tt OffersOnly-Ret

  -- the voter: two store READS and a VOTE deposit (`stPutVote`)
  oo-voter : ∀ n → OffersOnly noPuts (voter n)
  oo-voter n = OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt) (body k))
    where
    -- one pass, once the ranking block is in hand
    body : ∀ k b → OffersOnly noPuts
             (maybe′ (λ h → getBodyEv n h ⟶ (λ _ →
                        putVoteEv n ! mkVoteBlob (voterOf n) (rbHash b) ⟶ Ret (suc k)))
                     (Ret (suc k)) (announcedEB b))
    body k b with announcedEB b
    ... | nothing = OffersOnly-Ret
    ... | just h  =
      OffersOnly-Prefix (λ _ → tt) (λ _ → OffersOnly-Output tt OffersOnly-Ret)

  -- the submission thread: it deposits a TRANSACTION (`stPutTx`)
  oo-submit : ∀ n → OffersOnly noPuts (submit n)
  oo-submit n =
    OffersOnly-loop0 (OffersOnly-Prefix (λ _ → tt)
                        (λ _ → OffersOnly-Output tt OffersOnly-Skip))

  -- the certificate sink: one `stCert` read per pass
  oo-certSink : ∀ n → OffersOnly noPuts (certSink n)
  oo-certSink n = OffersOnly-loop0 (OffersOnly-Prefix (λ _ → tt) (λ _ → OffersOnly-Skip))

  -- one ChainSync server round, `NodeLogic.serverBody-k` verbatim: api events only
  oo-serverBody-k : ∀ n l d b → OffersOnly noPuts (serverBody-k n l d b)
  oo-serverBody-k n l d b =
    OffersOnly-Prefix₀ (λ _ → tt)
      (OffersOnly-Output tt
        (OffersOnly-Prefix (λ _ → tt) (λ _ →
          OffersOnly-Prefix₀ (λ _ → tt)
            (OffersOnly-Output tt
              (OffersOnly-Prefix₀ (λ _ → tt) OffersOnly-Skip)))))

  -- the ChainSync server thread
  oo-serverLoopL : ∀ n ld → OffersOnly noPuts (serverLoopL n ld)
  oo-serverLoopL n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix₀ (λ _ → tt)
      (OffersOnly-Prefix (λ _ → tt) (λ b →
        OffersOnly->>= (oo-serverBody-k n l (opposite d) b) (λ _ → OffersOnly-Ret))))

  -- the LN announce thread: a held-block read and an announcement
  oo-lnServerLoopL : ∀ n ld → OffersOnly noPuts (lnServerLoopL n ld)
  oo-lnServerLoopL n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt)
                             (λ b → OffersOnly-Output tt OffersOnly-Ret))

  -- the tx-closure gate: mempool READS only (`stGetTx`), so it keeps any `noPuts` continuation
  oo-awaitTxs : ∀ n (hs : List (TxHash × Size)) {P}
              → OffersOnly noPuts P → OffersOnly noPuts (awaitTxs n hs P)
  oo-awaitTxs n []             oo = oo
  oo-awaitTxs n ((h , _) ∷ hs) oo = OffersOnly-Prefix (λ _ → tt) (λ _ → oo-awaitTxs n hs oo)

  -- the body-offer thread: two store READS and two offers
  oo-bodyOfferLoop : ∀ n ld → OffersOnly noPuts (bodyOfferLoop n ld)
  oo-bodyOfferLoop n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt) (body k))
    where
    -- one pass, once the k-th oldest held block is in hand
    body : ∀ k b → OffersOnly noPuts
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
  oo-voteOfferLoop : ∀ n ld → OffersOnly noPuts (voteOfferLoop n ld)
  oo-voteOfferLoop n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt)
                             (λ v → OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ tt
                                      OffersOnly-Ret))

  -- the EB-serve thread: it READS a body out of the store and sends it
  oo-ebServeLoop : ∀ n ld → OffersOnly noPuts (ebServeLoop n ld)
  oo-ebServeLoop n (l , d) =
    OffersOnly-loop0 (OffersOnly-Prefix (λ _ → tt) (λ q →
      OffersOnly-Prefix (λ _ → tt) (λ eb → OffersOnly-Output tt OffersOnly-Skip)))

  -- the tx-closure server's reply builder: mempool READS and one send
  oo-serveTxs : ∀ n l d q bm acc → OffersOnly noPuts (serveTxs n l d q bm acc)
  oo-serveTxs n l d q []       acc =
    OffersOnly-Output ⦃ DecEq-TxsReply ⦄ tt OffersOnly-Skip
  oo-serveTxs n l d q (o ∷ os) acc with at? o (ebTxs (proj₁ q))
  ... | nothing      = oo-serveTxs n l d q os acc
  ... | just (h , _) = OffersOnly-Prefix (λ _ → tt)
                         (λ tx′ → oo-serveTxs n l d q os (acc ++ ((o , tx′) ∷ [])))

  -- the tx-closure-serve thread
  oo-ebTxsServeLoop : ∀ n ld → OffersOnly noPuts (ebTxsServeLoop n ld)
  oo-ebTxsServeLoop n (l , d) =
    OffersOnly-loop0 (OffersOnly-Prefix (λ _ → tt) (λ { (q , bm) →
      OffersOnly-Prefix (λ _ → tt) (λ _ → oo-serveTxs n l (opposite d) q bm []) }))

  -- every REQUESTED transaction pulled off the wire, deposited in the MEMPOOL; the
  -- membership guard only drops deposits, so both arms are `noPuts` — `oo-putChecked`'s shape
  oo-putAllTx : ∀ n ids txs → OffersOnly noPuts (putAllTx n ids txs)
  oo-putAllTx n ids []         = OffersOnly-Skip
  oo-putAllTx n ids (t′ ∷ txs) with memberOfNL (txHash t′) ids
  ... | true  = OffersOnly-Output tt (oo-putAllTx n ids txs)
  ... | false = oo-putAllTx n ids txs

  -- the TxSubmission pull thread
  oo-tsPull : ∀ n ld → OffersOnly noPuts (tsPull n ld)
  oo-tsPull n (l , d) =
    OffersOnly-loop0 (OffersOnly-Output ⦃ DecEq-ℕ×ℕ ⦄ tt
      (OffersOnly-Prefix (λ _ → tt) (λ ids →
        OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ tt
          (OffersOnly-Prefix (λ _ → tt) (λ txs → oo-putAllTx n ids txs)))))

  -- the TxSubmission serve thread: a mempool read and two replies
  oo-tsServe : ∀ n ld → OffersOnly noPuts (tsServe n ld)
  oo-tsServe n (l , d) =
    OffersOnly-loop (λ k → OffersOnly-Prefix (λ _ → tt) (λ _ →
      OffersOnly-Prefix (λ _ → tt) (λ tx′ →
        OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ tt
          (OffersOnly-Prefix (λ _ → tt) (λ _ →
            OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ tt OffersOnly-Ret)))))

  -- every checked entry of a tx-closure reply, deposited in the MEMPOOL
  oo-putChecked : ∀ n h es → OffersOnly noPuts (putChecked n h es)
  oo-putChecked n h []               = OffersOnly-Skip
  oo-putChecked n h ((o , tx′) ∷ es) with at? o (ebTxs h)
  ... | nothing      = oo-putChecked n h es
  ... | just (k , _) with ⌊ txHash tx′ ≟ k ⌋
  ...   | true  = OffersOnly-Output tt (oo-putChecked n h es)
  ...   | false = oo-putChecked n h es

  -- the reaction to a tx-closure offer: it blocks at the body (a READ) and deposits
  -- TRANSACTIONS, never a body
  oo-fetchTxs : ∀ n l d q → OffersOnly noPuts (fetchTxs n l d q)
  oo-fetchTxs n l d q =
    OffersOnly-Prefix (λ _ → tt) (λ _ →
      OffersOnly-Output ⦃ DecEq-TxsRequest ⦄ tt
        (OffersOnly-Prefix (λ _ → tt) (λ { (q′ , es) → guard q′ es })))
    where
    -- the echoed-point check around the deposit
    guard : ∀ q′ es → OffersOnly noPuts
              (putChecked n (proj₁ q) es ◁ ⌊ DecEq-EBPoint ._≟_ q′ q ⌋ ▷ Skip {0ℓ})
    guard q′ es with ⌊ DecEq-EBPoint ._≟_ q′ q ⌋
    ... | true  = oo-putChecked n (proj₁ q) es
    ... | false = OffersOnly-Skip

  -- every delivered vote blob, deposited in the VOTE store
  oo-putAllVotes : ∀ n vs → OffersOnly noPuts (putAllVotes n vs)
  oo-putAllVotes n []       = OffersOnly-Skip
  oo-putAllVotes n (v ∷ vs) = OffersOnly-Output tt (oo-putAllVotes n vs)

  ------------------------------------------------------------------------
  -- The BLOCK-depositing leaf that is vacuous here and CONTENT-BEARING for S4
  --
  -- It offers `stPut`, so it falls outside `noPuts` and is written at S1's own
  -- `noNeed`.  S4 cannot reuse it — it is one of the two leaves S4 has to prove
  -- something about; the other is `forgeL`, content-bearing for both.
  ------------------------------------------------------------------------

  -- the BlockFetch client thread: it deposits a BLOCK received off the wire
  oo-clientLoop : ∀ n ld → OffersOnly noNeed (clientLoop n ld)
  oo-clientLoop n (l , d) =
    OffersOnly-loop0 (OffersOnly-Prefix₀ (λ _ → λ ()) (OffersOnly-Prefix (λ _ → λ ()) k))
    where
    -- the reaction to one header: request the block, receive it, deposit it
    k : ∀ a → OffersOnly noNeed (clientBody-k n l d a)
    k (header b , _) =
      OffersOnly-Output (λ ())
        (OffersOnly-Prefix (λ _ → λ ()) (λ _ → OffersOnly-Output (λ ()) OffersOnly-Skip))

  ------------------------------------------------------------------------
  -- THE TWO CONTENT-BEARING LEAVES
  --
  -- The only two threads that ever deposit an EB body.  Each reaches its deposit
  -- through a chain whose EARLIER step minted the very hash the deposit needs — a gate
  -- that opens in the middle of a loop body, which is what `wfR-Prefix`/`wfR-Output`/
  -- `wf-loop` are for and what a state-independent alphabet cannot express.
  ------------------------------------------------------------------------

  -- THE FORGE THREAD.  `forgeBodyL` offers `putBodyEv n ! eb` only in the `just eb`
  -- branch, which is reached only after the `env … envForge` that MINTED `ebHash eb`
  -- one step earlier.  A forge carrying no EB deposits nothing, and a forge the block
  -- store rejects (`forgeOK` false) deposits nothing either.  The CERTIFICATE HALF the
  -- pass ends with — the `stHasCert` rendezvous and the ranking-block deposit — carries
  -- nothing S1 gates, so it is vacuous here; it is S4 that has to earn it.
  wf-forgeL : ∀ {ms} n → Wf fullα ms (forgeL n)
  wf-forgeL n = wf-loop0 (wfR-Prefix (λ _ _ _ → λ ()) (λ _ mb _ → pass mb))
    where
    -- the certificate half: an RB deposit, never an EB body
    oo-cert : ∀ b → OffersOnly noNeed (forgeCertL n b)
    oo-cert b with rbCert b
    ... | nothing = OffersOnly-Skip
    ... | just r  = OffersOnly-Prefix₀ (λ _ → λ ())
                      (OffersOnly-Output (λ ()) OffersOnly-Skip)

    -- the deposit, under the premise that the key is already minted.  The key is at
    -- `homeOf n`, which is where `putBodyEv n` fires.
    dep : ∀ {s} (me : Maybe LeiosEb) (b : Block)
        → (∀ eb → me ≡ just eb → memKey (homeOf n , ebHash eb) s ≡ true)
        → WfR fullα s (λ _ _ → ⊤) (forgeBodyL n (me , b))
    dep nothing   b h with forgeOK (nothing , b)
    ... | true  = wfR-free (oo-cert b) tt
    ... | false = wfR-free OffersOnly-Skip tt
    dep (just eb) b h with forgeOK (just eb , b)
    ... | false = wfR-free OffersOnly-Skip tt
    ... | true  = wfR-Output (λ le _ → λ { refl → memKey-mono le (h eb refl) })
                             (λ _ _ → wfR-free (oo-cert b) tt)

    -- THE MINT: the forge event itself puts `(homeOf n , ebHash eb)` in the minted set,
    -- so the state its continuation runs at already contains it.  `forgeEv n` fires at
    -- `homeOf n`, so the mint's own endpoint IS the deposit endpoint and record η closes
    -- the bookkeeping definitionally — no `endpoints-sound` is needed on this branch.
    mint : ∀ {s} (me : Maybe LeiosEb) (b : Block) (eb : LeiosEb) → me ≡ just eb
         → memKey (homeOf n , ebHash eb) (bodyNext (lbl (forgeEv n) (me , b)) s) ≡ true
    mint {s} .(just eb) b eb refl =
      ∈→memKey (homeOf n , ebHash eb) ((homeOf n , ebHash eb) ∷ s) (here refl)

    -- one pass of the forge thread, at the state the forge event led to
    pass : ∀ {s} (mb : Maybe LeiosEb × Block)
         → WfR fullα (bodyNext (lbl (forgeEv n) mb) s) (λ _ _ → ⊤) (forgeBodyL n mb)
    pass (me , b) = dep me b (mint me b)

  -- THE NOTIFY CLIENT.  Its ONE body deposit is inside `fetchBody`, under the wire
  -- guard `⌊ ebHash eb ≟ proj₁ q ⌋`, where `q` is the point this very thread sent on
  -- `lfpSendBlockRequest` — the step that MINTED `proj₁ q`.  The guard's witness turns
  -- the deposit's obligation into that mint.  The other three branches deposit an EB
  -- ENTRY, TRANSACTIONS and VOTE BLOBS respectively, none of which S1 gates.
  -- IT TAKES THE ENDPOINT'S MEMBERSHIP: the request mints at `homeAt (l , d)` and the
  -- deposit it licenses is at `homeOf n`, so the leaf has to know that `(l , d)` really
  -- is one of `n`'s endpoints.
  wf-lnClient : ∀ {ms} n ld → ld ∈ endpointsList n → Wf fullα ms (lnClientLoopL n ld)
  wf-lnClient n (l , d) mem = wf-loop0 (wfR-Prefix (λ _ _ _ → λ ()) (λ _ _ _ → choice))
    where
    -- the announcement branch: a no-op
    annB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
             (apiLP l d lnpRecvBlockAnnouncement ⟶ (λ _ → Skip))
    annB = wfR-free (OffersOnly-Prefix (λ _ → λ ()) (λ _ → OffersOnly-Skip)) tt

    -- THE GUARDED DEPOSIT: the body is stored only if it hashes to the requested point,
    -- and that point is in the minted set by the premise
    dep : ∀ {s} (q : EBHash × LSlot) (eb : LeiosEb) → memKey (homeOf n , proj₁ q) s ≡ true
        → WfR fullα s (λ _ _ → ⊤)
            ((putBodyEv n ! eb ⟶ Skip {0ℓ}) ◁ ⌊ ebHash eb ≟ proj₁ q ⌋ ▷ Skip {0ℓ})
    dep q eb h with ebHash eb ≟ proj₁ q
    ... | no  _  = wfR-free OffersOnly-Skip tt
    ... | yes pr =
      wfR-Output (λ {s′} le _ → λ { refl →
                    mem-≡ (homeOf n) (ebHash eb) (proj₁ q) s′ pr (memKey-mono le h) })
                 (λ _ _ → wfR-free OffersOnly-Skip tt)

    -- A REQUEST AT THIS ENDPOINT MINTS AT THIS NODE'S OWN DEPOSIT ENDPOINT.  The mint is
    -- keyed by `homeAt (l , d)`, i.e. `homeOf (endAt l d)`, and `endAt l d` IS `n` because
    -- `(l , d)` is one of `n`'s endpoints — `Topology.endpoints-sound`, through
    -- `sound-at`.  THIS is the one leaf the threaded membership is spent at.
    atHome : ∀ (h : EBHash) (ms : Minted) → (homeAt (l , d) , h) ∈ ms
           → memKey (homeOf n , h) ms ≡ true
    atHome h ms q =
      ∈→memKey _ _ (subst (λ z → (z , h) ∈ ms) (cong homeOf (sound-at n l d mem)) q)

    -- the reaction to one body offer: the request MINTS `(homeOf n , proj₁ q)`, the reply
    -- mints nothing, and the deposit spends the mint
    fetch : ∀ {s} (qs : (EBHash × LSlot) × Size)
          → WfR fullα s (λ _ _ → ⊤) (fetchBody n l d qs)
    fetch (q , sz) =
      wfR-Output (λ _ _ → λ ())
        (λ _ _ → wfR-Prefix (λ _ _ _ → λ ())
                   (λ le eb _ → dep q eb (atHome (proj₁ q) _ (le (here refl)))))

    -- the body-offer branch
    offB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
             (apiLP l d lnpRecvBlockOffer ⟶ fetchBody n l d)
    offB = wfR-Prefix (λ _ _ _ → λ ()) (λ _ qs _ → fetch qs)

    -- the tx-closure branch: transactions, not bodies
    txB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
            (apiLP l d lnpRecvBlockTxsOffer ⟶ fetchTxs n l d)
    txB = wfR-free (OffersOnly-Prefix (λ _ → λ ())
                     (λ q → oo↓ (oo-fetchTxs n l d q))) tt

    -- the votes branch: vote blobs, not bodies
    votB : ∀ {s} → WfR fullα s (λ _ _ → ⊤) (apiLP l d lnpRecvVotes ⟶ putAllVotes n)
    votB = wfR-free (OffersOnly-Prefix (λ _ → λ ())
                      (λ vs → oo↓ (oo-putAllVotes n vs))) tt

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
      (wf-⦀ (wf-nP (oo-serverLoopL n e))
      (wf-⦀ (wf-lnClient n e mem)
      (wf-⦀ (wf-nP (oo-lnServerLoopL n e))
      (wf-⦀ (wf-nP (oo-bodyOfferLoop n e))
      (wf-⦀ (wf-nP (oo-voteOfferLoop n e))
      (wf-⦀ (wf-nP (oo-ebServeLoop n e))
      (wf-⦀ (wf-nP (oo-ebTxsServeLoop n e))
      (wf-⦀ (wf-nP (oo-tsPull n e)) (wf-nP (oo-tsServe n e))))))))))

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
    wf-⦀ (wf-forgeL n)
      (wf-⦀ (wf-nP (oo-ebIndex n))
      (wf-⦀ (wf-nP (oo-voter n))
      (wf-⦀ (wf-nP (oo-submit n))
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

  -- S1 — BODY ORIGIN, node-local.  A node running `nodeLogicL` from empty stores stores
  -- no EB body it neither forged nor asked for AT ONE OF ITS OWN ENDPOINTS.  LEVEL:
  -- node — `Leios.BodySystemL` lifts this to the whole network.  The form "every body
  -- held anywhere was forged somewhere" is still NOT proved: see the module header for
  -- the full list of what this does not rule out.
  BodySound : Set₁
  BodySound = ∀ (n : Node) → BodySpecT ⊑T nodeP n (nodeLogicL n st₀)

  -- S1 FOR ANY LOGIC THAT CARRIES THE GATE AND NEVER RETURNS, INSIDE THE BUNDLE.  The
  -- bundle and the logic compose on `apiES` at the full guarantee alphabet (`Sep apiES`
  -- is trivial there), and `wf→osafe` then `osafe→⊑T` turn that one `Wf` fact into the
  -- trace refinement.
  soundOf : ∀ n (lg : Proc) → Wf fullα [] lg → NoRet lg → BodySpecT ⊑T nodeP n lg
  soundOf n lg w nr =
    osafe→⊑T (wf→osafe (wf-mono-G (λ _ _ _ → inj₁ tt)
                         (wf-Par apiES sep-api (wf-linkBundlesP n) w))
                       (NoRet-ParR apiES nr))

  -- … and the same WITHOUT the peer bundle, for a composite stated at the node logic
  -- alone.  This is the load-bearing half of `soundOf`: the bundle contributes only
  -- `wf-linkBundlesP`, which is vacuous (no peer offers a `store` channel).
  soundLogic : ∀ (lg : Proc) → Wf fullα [] lg → NoRet lg → BodySpecT ⊑T lg
  soundLogic lg w nr = osafe→⊑T (wf→osafe w nr)

  -- S1, PROVED, at the shipped node logic from empty stores
  bodySound : BodySound
  bodySound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)

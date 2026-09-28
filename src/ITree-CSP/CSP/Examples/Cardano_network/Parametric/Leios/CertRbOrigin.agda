{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S4, CERTIFICATE-RB ORIGIN: a node deposits a
-- ranking block whose body carries a certificate only if it had already
-- certified the ranking block that certificate names, or the block came off
-- the wire.
--
-- WHAT S4 SAYS.  A node running `nodeLogicL` from empty stores performs
-- `store home(n) stPut ! b` with `rbCert b = just r` only when `r` is
--
--   * an RB hash this node has already certified — the
--     `store home(n) (stHasCert r)` rendezvous, offered by `voteStore` only
--     for the hashes in its `certs` list; or
--   * the certificate hash of a block this node received off the wire at
--     `apiBF l d recvBFBlock` — the node relays what it is given.
--
-- STATED PRECISELY, so that nothing rests on an injectivity that is not
-- assumed.  The key is `RbHash` and the two tests are PROPOSITIONAL EQUALITY
-- of `RbHash` values under `decRbHash` — no hash function is inverted and
-- none is assumed injective, so the `stHasCert` clause really does name the
-- same `r`.  The WIRE clause is weaker than "this very block arrived": what
-- is minted is the delivered block's `rbCert` VALUE, so a DIFFERENT block
-- carrying the SAME certificate hash is licensed by that delivery.  And the
-- `stHasCert r` clause says only that the label occurred; that the node's
-- vote store is what offered it is a property of the composite (no store but
-- `voteStore` offers `stHasCert`), not something this discipline proves, and
-- whether the certification behind it was earned is S3's business.
--
-- ============ THE SCOPE OF S4 — READ BEFORE QUOTING IT ============
--
-- S4 IS A FORGE-ROUTE STATEMENT (the ruling recorded verbatim at
-- `NodeLogicL.agda:264-273`): every cert-RB that enters `held` BY THE FORGE
-- ROUTE was preceded by a local `stCert` for the RB its `rbCert` names.  IT
-- IS NOT A STATEMENT ABOUT `held` AS A WHOLE.  `storeStepL`'s `putEv` branch
-- is UNGATED and `NodeLogic.clientBody-k` deposits through it ANY block
-- received off the wire, certificate-carrying or not — which spec §4.5
-- requires, a cert-RB "diffuses like any RB".  THE WIRE ROUTE IS DELIBERATELY
-- UNGATED, and this module makes that explicit by MINTING at
-- `apiBF _ _ recvBFBlock`: a delivered block licenses its own deposit.
-- Never state S4 as "only `forgeCert` can put a cert-RB in `held`".
--
-- WHAT S4 DOES **NOT** RULE OUT.
--   * THE WIRE ROUTE, explicitly (above).  A neighbour may hand this node any
--     certificate-carrying block at all and it is stored.  S4 constrains what
--     a node INVENTS, not what it accepts.  And because the wire clause mints
--     a HASH and not a block, one delivery licenses the deposit of every
--     block carrying that same certificate hash.
--   * It says nothing about whether the certificate is JUSTIFIED: the
--     `stHasCert r` rendezvous only reports that this node's own vote store
--     fired `stCert r`, and S3 is what constrains THAT.  Whether the blobs
--     behind it were really cast is S2/S2′'s business, and nothing here says
--     the RB `r` is one this node holds.
--   * It says nothing about the other four stores (`stPutBody`, `stPutEB`,
--     `stPutTx`, `stPutVote`) — S1, S2 and S2′ own those — nor about a
--     CERTIFICATE-FREE block, which `certRbGate` licenses outright.
--   * It says nothing about OTHER nodes (see the endpoint caveat below).
--   * It is purely safety-shaped: see the REACHABILITY NOTE below.
--
-- ============ REACHABILITY NOTE (Task 10's finding, REPAIRED in R1) ============
--
-- `forgeCert`'s first event is `env home(n) envForgeCert`.  That channel is
-- INSIDE `storeES` (`NodeLogic.storeSet` maps every `env` channel to `⊤`), and
-- under `∥⇘ storeES ⇙` a synchronised event fires only when BOTH operands offer
-- it (`CSP.Operators.par-pVis`, the `yes _ | _ | _ = nothing` clause).  AS
-- ORIGINALLY SHIPPED NO STORE OFFERED IT — `storeStepL` offered `envForge` and
-- `envForgeCert` occurred nowhere else in the estate — so inside
-- `nodeLogicL n st₀` the whole `forgeCert` thread was BLOCKED AT ITS FIRST
-- EVENT, as was `submit`, and the forge route this theorem constrains was
-- UNREACHABLE rather than merely unexercised.
--
-- THAT DEFECT IS FIXED.  `NodeLogicL.storeStepL` now carries a pure-rendezvous
-- `envForgeCert` arm (and `memStep` an `envSubmit` one), and
-- `Leios/NodeLogicLSanity.forgeCert-first-step` exhibits the first step of the
-- forge route INSIDE the full `nodeLogicL nA st₀` as an LTS derivation.  So S4
-- now constrains a route the composite can actually take, and the deposit at
-- the end of it is still earned only through the `stHasCert r` rendezvous.
-- `NodeLogicLSanity.uncertified-blocks`/`certified-offers` probe that at ONE
-- hash, on the ISOLATED `voteStore`: they are not the ∀ statement.  The ∀
-- fact — the store offers `stHasCert r` exactly for the `r` in its `certs`
-- list — is structural in `NodeLogicL.offerCerts` and is read off that
-- definition, not proved by those two probes.
-- NOTE FOR ANY WRITE-UP that quotes the older, blocked-thread wording (ledger
-- entries up to 2026-09-23, `Laws_status` limitation 3): it described the model
-- before this repair and is now historical.
--
-- "ITS OWN CERTIFICATE" IS A NODE-LEVEL READING — READ THIS BEFORE ANY SYSTEM
-- LIFT.  Like S1's, S2's, S2′'s and S3's, this discipline is ENDPOINT-AGNOSTIC
-- in its mints: `certRbMints` mints at EVERY link and direction and `isPut`
-- ignores the endpoint of the deposit.  At NODE level the two coincide, for
-- the reason `VoteSound`'s header records: inside `nodeP n (nodeLogicL n st₀)`
-- the only `store`/`env` channels that occur are the `homeOf n` ones and no
-- peer of the bundle offers a `store` channel at all.  A system lift would let
-- node X's certificate licence node Y's deposit; the fix is to index the key
-- by `(l , d)` and gate a `stPut` at `(l , d)` on keys carrying that same
-- `(l , d)`, exactly as S2's header prescribes.
--
-- HOW IT IS PROVED.  S1's/S2's assume-guarantee route — `BlockProvenance`'s
-- `Carrier` plus `BlockProvenanceWfR.Body`, the shared leaves of
-- `OriginLeaves`, and `wf→osafe` back into `OriginSafe`.  THE GATED CHANNEL IS
-- EMITTED BY THREADS (`forgeCert` and the BlockFetch `clientLoop`), never by a
-- store, so this is S2's ORIENTATION and not S3's: the thread group carries
-- `fullα`, the store group `∅α`, the `Sep` is `sep-store`, and the assembly is
-- `wf-withStores`.
--
-- THE `noPuts` TRANSPORT.  Eighteen of the twenty leaves — twelve threads and
-- six helpers — are NOT written here: `BodyOrigin` proves them at the shared
-- alphabet `noPuts` ("this channel is neither `stPut` nor `stPutBody`"), and
-- three lines (`nP→noNeed`/`oo↓`/`wf-nP`) turn each into an S4 leaf.  What is
-- written here is the four leaves outside `noPuts` — vacuity for `forgeL` and
-- for the Notify client, which deposit an EB BODY — and the two
-- CONTENT-BEARING ones, `forgeCert` and `clientLoop`.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Leios.CertRbOrigin where

open import Level using (Level; 0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; opposite)
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
import CSP.Examples.Cardano_network.Parametric.Leios.BodyOrigin as BO

-- the S4 origin discipline, parametric in the network parameters, the Leios parameters,
-- the topology, the api alphabet and the node-to-voter map — exactly the five parameters
-- `NodeLogicL.Generic` takes, so `nodeLogicL` below is literally its own
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open Params p
    using ( Block; LSlot; VoterId; VoteBlob; EB; EBHash; RbHash; Tx; TxHash; Size
          ; linkConfig; ebHash; rbHash; txHash; slotOf; announcedEB
          ; decBlock; decEBHash; decRbHash; decLSlot; decVoteBlob; decEB; decTx; decTxHash )
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
          ; envForge; envSubmit; envForgeCert
          ; recvBFBlock
          ; lnpSendBlockOffer; lnpSendBlockTxsOffer
          ; lnpRecvBlockAnnouncement; lnpRecvBlockOffer; lnpRecvBlockTxsOffer
          ; lnpRecvVotes
          ; lfpSendBlockRequest; lfpSendBlockTxsRequest; lfpSendBlock; lfpSendBlockTxs
          ; lfpRecvBlock; lfpRecvBlockTxs; lfpReqBlockRequest; lfpReqBlockTxsRequest )
  -- `decRbHash` is the ONE `DecEq RbHash` in scope here, so `memberOf` at the key type
  -- resolves to exactly the term the gate was built with (ledger gotcha 4).  No `DecEq`
  -- instance is DECLARED for it: at `leiosLParams` `RbHash = Maybe Bool` and a declared
  -- instance would clash with stdlib's `DecEq-Maybe` (the Task-7 ruling).
  open D p
    using ( Payload; Point; Header; Tip; Vote; point; header; vote; TxBitmap
          ; DecEq-Point; DecEq-Header; DecEq-Tip; DecEq-ChainRange; DecEq-Payload
          ; DecEq-Vote; DecEq-EBPoint; DecEq-TxBitmap; DecEq-TxEntries
          ; DecEq-TxsRequest; DecEq-TxsReply; DecEq-Offer )
  -- (wholesale, as `NetworkPar` and `OriginLeaves`: `Dir`, its decidable equality and
  -- the six `IDs` constructors)
  open import CSP.Examples.Cardano_network.Base
  open Topology t using (Node; endpointsOf)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (EventSet; Skip; Ret; _⦀_; _∥⇘_⇙_; Prefix; Prefix₀; Output; _□_; _◁_▷_)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES
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
          ; putTxEv; getTxAtEv; getTxEv; hasCertEv; forgeCertEv; forgeOK
          ; forgeL; forgeBodyL; forgeCert; ebIndex; voter; submit; certSink
          ; serverLoopL; lnServerLoopL; bodyOfferLoop; voteOfferLoop
          ; ebServeLoop; ebTxsServeLoop; serveTxs; putChecked; tsPull; tsServe; putAllTx
          ; lnClientLoopL; fetchBody; fetchTxs; putAllVotes
          ; endpointThreadsL; allThreadsL )
  open OS using (memberOf; memberOf-mono; ∈→memberOf)
  open OS.Generic p t apiES using (noRet→noTick)
  -- the PROTOTYPE peer bundle, whose nine `Wf` facts live in `OriginLeaves.Leaves`
  open import CSP.Examples.Cardano_network.Parametric.Leios.PeersP p using (nodeBundleP)
  -- THE TRANSPORT (Task 9's gift): the vacuous leaves proved at `BodyOrigin`'s `noPuts`,
  -- which excludes BOTH thread-emitted store deposits, hence also S4's.  FOURTEEN of the
  -- block's eighteen definitions are named here; the other four (`oo-serverBody-k`,
  -- `oo-serveTxs`, `oo-putAllTx`, `oo-putChecked`) are helpers already spent INSIDE
  -- these, so S4 gets them without naming them.  An EXPLICIT `using` list, not a
  -- wholesale open: `BodyOrigin.Generic` declares `instance DecEq-Header×Tip`, which
  -- would compete here.
  open BO.Generic p lp t apiES voterOf
    using ( noPuts; oo-ebIndex; oo-voter; oo-submit; oo-certSink
          ; oo-serverLoopL; oo-lnServerLoopL; oo-bodyOfferLoop; oo-voteOfferLoop
          ; oo-ebServeLoop; oo-ebTxsServeLoop; oo-tsPull
          ; oo-tsServe; oo-fetchTxs; oo-putAllVotes )

  ------------------------------------------------------------------------
  -- The origin discipline
  ------------------------------------------------------------------------

  -- IS THIS THE BLOCK-DEPOSIT CHANNEL, and if so which block?  The ONE channel dispatch
  -- of the discipline: the gate and the carrying relation both route through it, so each
  -- is discharged by a two-clause case on this `Maybe` instead of a thirty-two-clause
  -- alphabet enumeration (`needs-put` still writes that enumeration once, because its
  -- conclusion is a Σ about the channel).
  isPut : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Maybe Block
  isPut (_ , store _ _ stPut) b = just b
  isPut _                     _ = nothing

  -- WHAT MINTS.  The vote store vouching that `r` is already certified HERE — the
  -- `stHasCert r` rendezvous, offered only for the hashes in its `certs` list — and a
  -- BlockFetch delivery of a block that carries a certificate: the node relays what it is
  -- given, and S4 constrains what it INVENTS (the forge-route scope, module header).
  -- ENDPOINT-AGNOSTIC (link and direction are `_`): see the header before lifting this
  -- above node level.
  certRbMints : (at : AnyTypes (Net_Api Payload)) → proj₁ at → List RbHash
  certRbMints (_ , store _ _ (stHasCert r)) _ = r ∷ []
  certRbMints (_ , apiBF _ _ recvBFBlock)   b = maybe′ (λ r → r ∷ []) [] (rbCert b)
  certRbMints _                             _ = []

  -- IS THIS DEPOSIT LICENSED?  A certificate-free block is free; a certificate-carrying
  -- one needs the RB hash its certificate names to have been minted.
  vouchedRb : List RbHash → Block → Bool
  vouchedRb ms b = maybe′ (λ r → memberOf r ms) true (rbCert b)

  -- WHAT IS GATED: only a ranking-block deposit, and only by `vouchedRb`.  Everything
  -- else is free — in particular every other store deposit (see the module header).
  certRbGate : List RbHash → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Bool
  certRbGate ms at a = maybe′ (vouchedRb ms) true (isPut at a)

  -- monotonicity of the membership test under the block's optional certificate
  mem-mono-maybe : ∀ {ms ms′} → ms ⊆ ms′ → (z : Maybe RbHash)
                 → maybe′ (λ r → memberOf r ms)  true z ≡ true
                 → maybe′ (λ r → memberOf r ms′) true z ≡ true
  mem-mono-maybe sub nothing  eq = refl
  mem-mono-maybe sub (just r) eq = memberOf-mono sub eq

  -- the gate's monotonicity, as a case on `isPut`'s answer alone: the only
  -- state-dependent test is `memberOf`, which is monotone
  gate-mono-aux : ∀ {ms ms′} → ms ⊆ ms′ → (z : Maybe Block)
                → maybe′ (vouchedRb ms)  true z ≡ true
                → maybe′ (vouchedRb ms′) true z ≡ true
  gate-mono-aux sub nothing  eq = refl
  gate-mono-aux sub (just b) eq = mem-mono-maybe sub (rbCert b) eq

  -- MINTING ONLY EVER OPENS THE GATE
  certRbGate-mono : ∀ {ms ms′} → ms ⊆ ms′
                  → ∀ at a → certRbGate ms at a ≡ true → certRbGate ms′ at a ≡ true
  certRbGate-mono sub at a eq = gate-mono-aux sub (isPut at a) eq

  ------------------------------------------------------------------------
  -- The specification S4 names
  ------------------------------------------------------------------------

  -- the generic carrier at the S4 discipline.  `OriginSpecT` is renamed rather than
  -- listed: Agda rejects a name that appears in both `using` and `renaming`.
  open OS.Generic.Origin p t apiES RbHash decRbHash certRbMints certRbGate certRbGate-mono
    using ( Minted; mintedAfter; mintedAfter-⊇; originOffer; OriginSpecAt; specAt-init
          ; OSafe; gateOK; onτ; onEv; noTick; osafe→⊑T )
    renaming (OriginSpecT to CertRbSpecT)
    public

  ------------------------------------------------------------------------
  -- The assume-guarantee instance, and the ONE alphabet enumeration
  ------------------------------------------------------------------------

  -- WHAT A LABEL CARRIES: a block deposit carries the RB hash its certificate names,
  -- when it has one; nothing else carries anything.  (This is the `Carries` of the Wf
  -- framework — "needs a justification" — NOT the same thing as `certRbMints`.)
  certRbCarries : (at : AnyTypes (Net_Api Payload)) → proj₁ at → RbHash → Set
  certRbCarries at a r = maybe′ (λ b → rbCert b ≡ just r) ⊥ (isPut at a)

  -- WHAT THE MINTED SET MUST SAY ABOUT A CARRIED HASH: it was certified or delivered here
  certRbWA : Minted → RbHash → Set
  certRbWA ms r = memberOf r ms ≡ true

  -- the state a label leads to: EXACTLY `OriginSafe`'s `mintedAfter` on a visible label
  -- (definitionally), unchanged on τ and `√`
  certRbNext : Label (⊤ {0ℓ}) → Minted → Minted
  certRbNext (ev (evl (evLabel X e a))) ms = certRbMints (X , e) a ++ ms
  certRbNext _                          ms = ms

  -- the minted set only grows
  certRbNext-⊆ : ∀ a ms → ms ⊆ certRbNext a ms
  certRbNext-⊆ (ev (evl (evLabel X e a))) ms = mintedAfter-⊇ (X , e) a
  certRbNext-⊆ (ev (√ _))                 ms = λ q → q
  certRbNext-⊆ τ                          ms = λ q → q

  -- EVERY CARRYING CHANNEL IS THE BLOCK DEPOSIT.  One clause per `Net_Api` constructor
  -- and, under `store`, one per `StoreTag` — 32 in all — because `isPut`'s catch-all does
  -- not reduce until the constructor is known.  This is the whole alphabet tax of S4, and
  -- it does double duty: `needs-store` and `nP→noNeed` both fall out of it.
  needs-put : ∀ {X} {e : Net_Api Payload X} {a : X} {r} → certRbCarries (X , e) a r
            → Σ[ l ∈ Link ] Σ[ d ∈ Dir ]
                (_≡_ {A = AnyTypes (Net_Api Payload)}
                     (X , e) (StoreCar stPut , store l d stPut))
  needs-put {e = store l d stPut}           _  = l , d , refl
  needs-put {e = store _ _ stGet}           ()
  needs-put {e = store _ _ (stGetAt _)}     ()
  needs-put {e = store _ _ stPutEB}         ()
  needs-put {e = store _ _ (stGetEBAt _)}   ()
  needs-put {e = store _ _ stPutBody}       ()
  needs-put {e = store _ _ (stGetBody _)}   ()
  needs-put {e = store _ _ stPutTx}         ()
  needs-put {e = store _ _ (stGetTxAt _)}   ()
  needs-put {e = store _ _ stPutVote}       ()
  needs-put {e = store _ _ (stGetVoteAt _)} ()
  needs-put {e = store _ _ stCert}          ()
  needs-put {e = store _ _ (stGetTx _)}     ()
  needs-put {e = store _ _ (stHasCert _)}   ()
  needs-put {e = input _ _ _}               ()
  needs-put {e = output _ _ _}              ()
  needs-put {e = sndmsg _ _ _}              ()
  needs-put {e = rcvmsg _ _ _}              ()
  needs-put {e = tx _ _ _}                  ()
  needs-put {e = sndack _ _ _}              ()
  needs-put {e = rcvack _ _ _}              ()
  needs-put {e = ack _ _ _}                 ()
  needs-put {e = done _ _ _}                ()
  needs-put {e = apiCS _ _ _}               ()
  needs-put {e = apiBF _ _ _}               ()
  needs-put {e = apiTS _ _ _}               ()
  needs-put {e = apiKA _ _ _}               ()
  needs-put {e = apiLN _ _ _}               ()
  needs-put {e = apiLF _ _ _}               ()
  needs-put {e = apiLP _ _ _}               ()
  needs-put {e = env _ _ _}                 ()
  needs-put {e = break _}                   ()

  -- … weakened to the "some store tag" form `OriginLeaves` asks for
  needs-store : ∀ {X} {e : Net_Api Payload X} {a : X} {r} → certRbCarries (X , e) a r
              → Σ[ l ∈ Link ] Σ[ d ∈ Dir ] Σ[ m ∈ StoreTag ]
                  (_≡_ {A = AnyTypes (Net_Api Payload)}
                       (X , e) (StoreCar m , store l d m))
  needs-store {X} {e} {a} {r} c with needs-put {X} {e} {a} {r} c
  ... | l , d , refl = l , d , stPut , refl

  -- THE SHARED LEAVES: the vacuous-leaf lemmas at both carriers, the two guarantee
  -- alphabets and their `Sep`s, and the prototype peer bundle
  open OL.Generic.Leaves p t apiES Minted RbHash certRbCarries certRbWA certRbNext
                         _⊆_ ⊆-refl ⊆-trans certRbNext-⊆ needs-store

  -- the assume-guarantee carrier at the S4 discipline …
  open BP.Carrier (Net_Api-≟ {Payload}) Minted RbHash certRbCarries certRbWA
                  certRbNext _⊆_ ⊆-trans certRbNext-⊆
    using ( OK; lbl; Wf; nowW; stepW; wf-mono; wf-mono-G; wf-Skip; wf-deadlock
          ; Sep; _∪α_; wf-Par; wf-⦀; wf-⦀⋆ )

  -- … and its returning-tree layer, at the SAME arguments, so the two `Wf`s are the
  -- same record
  open BPW.Body (Net_Api-≟ {Payload}) Minted RbHash certRbCarries certRbWA
                certRbNext _⊆_ ⊆-refl ⊆-trans certRbNext-⊆
    using ( WfR; nowR; stepR; retR; Stable; stable-node; stable-□
          ; wfR-mono; wfR-Ret; wfR-Stop; wfR-Prefix; wfR-Output; wfR-⊓; wfR-□
          ; wfR->>=; wf-loop; wf-loop0; wf-⦀⁺ )

  ------------------------------------------------------------------------
  -- THE BRIDGE
  ------------------------------------------------------------------------

  -- the gate at a deposit, from the deposit's `OK` obligation, as a case on the block's
  -- optional certificate
  gate-ok-mb : (ms : Minted) (z : Maybe RbHash)
             → (∀ {r} → z ≡ just r → memberOf r ms ≡ true)
             → maybe′ (λ r → memberOf r ms) true z ≡ true
  gate-ok-mb ms nothing  g = refl
  gate-ok-mb ms (just r) g = g refl

  -- `OK` at a block deposit IS the gate, and at every other channel the gate is `true`
  gate-ok-aux : (ms : Minted) (z : Maybe Block)
              → (∀ {r} → maybe′ (λ b → rbCert b ≡ just r) ⊥ z → memberOf r ms ≡ true)
              → maybe′ (vouchedRb ms) true z ≡ true
  gate-ok-aux ms nothing  g = refl
  gate-ok-aux ms (just b) g = gate-ok-mb ms (rbCert b) g

  -- `OK` at a label IS the gate
  ok→gate : ∀ {X} {e : Net_Api Payload X} {a : X} {ms}
          → (∀ {r} → certRbCarries (X , e) a r → certRbWA ms r)
          → certRbGate ms (X , e) a ≡ true
  ok→gate {X} {e} {a} {ms} f = gate-ok-aux ms (isPut (X , e) a) f

  -- A `Wf` FACT ON THE FULL ALPHABET IS AN `OSafe` FACT.  The two carriers agree by
  -- construction: `certRbNext` on a visible label IS `mintedAfter`, `OK` at a label IS
  -- the gate (`ok→gate`), and `Wf` on `fullα` guarantees it for every label.  `OSafe`'s
  -- `noTick` comes from `NoRet`, which belongs to the COMPOSITE, not to the peer bundle,
  -- which does return.
  wf→osafe : ∀ {ms} {M : Proc} → Wf fullα ms M → NoRet M → OSafe ms M
  wf→osafe {ms = ms} w nr .gateOK {X} {e} {a} st =
    ok→gate {X} {e} {a} {ms} (nowW w ⊆-refl tt st)
  wf→osafe w nr .onτ    st = wf→osafe (stepW w ⊆-refl st tt) (NoRet.stepNR nr st)
  wf→osafe w nr .onEv   st =
    wf→osafe (stepW w ⊆-refl st (nowW w ⊆-refl tt st)) (NoRet.stepNR nr st)
  wf→osafe w nr .noTick st = noRet→noTick nr st

  ------------------------------------------------------------------------
  -- THE `noPuts` TRANSPORT — three lines, and eighteen leaves come across
  ------------------------------------------------------------------------

  -- everything S4's `Carries` speaks about is a `store … stPut`, which `noPuts` excludes.
  -- ALL FOUR IMPLICITS ARE PINNED ON BOTH SIDES: `certRbCarries` is `maybe′`-defined and
  -- therefore non-injective, so an unpinned `with` dies in `UnificationStuck` (Task 8).
  nP→noNeed : ∀ at a → noPuts at a → noNeed at a
  nP→noNeed (X , e) a np {r} c with needs-put {X} {e} {a} {r} c
  ... | l , d , refl = np

  -- a thread confined to `noPuts` carries nothing for S4 …
  oo↓ : ∀ {ℓr} {R : Set ℓr} {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
      → OffersOnly noPuts M → OffersOnly noNeed M
  oo↓ = OffersOnly-mono nP→noNeed

  -- … and is therefore a `Wf` leaf at every guarantee alphabet and every state
  wf-nP : ∀ {G ms} {M : Proc} → OffersOnly noPuts M → Wf G ms M
  wf-nP oo = wf-free (oo↓ oo)

  ------------------------------------------------------------------------
  -- The four leaves OUTSIDE `noPuts`: vacuous for S4, content-bearing for S1
  --
  -- `forgeL` and the Notify client deposit an EB BODY (`stPutBody`), which `noPuts`
  -- excludes and S4 does not gate, so they are written here at S4's own `noNeed`.
  ------------------------------------------------------------------------

  -- the forge thread: `env … envForge`, then at most an EB-BODY deposit — never a block
  oo-forgeL : ∀ n → OffersOnly noNeed (forgeL n)
  oo-forgeL n = OffersOnly-loop0 (OffersOnly-Prefix (λ _ → λ ()) body)
    where
    -- the body deposited by one forge, under the forge guard and the optional EB
    body : ∀ mb → OffersOnly noNeed (forgeBodyL n mb)
    body (me , b) with forgeOK (me , b)
    ... | false = OffersOnly-Skip
    ... | true with me
    ...   | nothing = OffersOnly-Skip
    ...   | just eb = OffersOnly-Output (λ ()) OffersOnly-Skip

  -- the guarded EB-BODY deposit of a fetch: not a block either way
  oo-fetchDep : ∀ n h′ eb
              → OffersOnly noNeed
                  ((putBodyEv n ! eb ⟶ Skip {0ℓ}) ◁ ⌊ ebHash eb ≟ h′ ⌋ ▷ Skip {0ℓ})
  oo-fetchDep n h′ eb with ⌊ ebHash eb ≟ h′ ⌋
  ... | true  = OffersOnly-Output (λ ()) OffersOnly-Skip
  ... | false = OffersOnly-Skip

  -- the reaction to a body offer: request the offered point, receive the body, deposit
  -- it if it hashes to what was asked for — an EB body, never a ranking block
  oo-fetchBody : ∀ n l d qs → OffersOnly noNeed (fetchBody n l d qs)
  oo-fetchBody n l d (q , _) =
    OffersOnly-Output ⦃ DecEq-EBPoint ⦄ (λ ())
      (OffersOnly-Prefix (λ _ → λ ()) (oo-fetchDep n (proj₁ q)))

  -- THE NOTIFY CLIENT: four branches after the long-poll request, none of which deposits
  -- a RANKING BLOCK.  Stated at the `Wf` layer rather than as an `OffersOnly` fact
  -- because the four-way `□` needs `wfR-□`'s stability side conditions.
  wf-lnClient : ∀ {ms} n ld → Wf fullα ms (lnClientLoopL n ld)
  wf-lnClient n (l , d) = wf-loop0 (wfR-Prefix (λ _ _ _ → λ ()) (λ _ _ _ → choice))
    where
    -- the announcement branch: a no-op
    annB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
             (apiLP l d lnpRecvBlockAnnouncement ⟶ (λ _ → Skip))
    annB = wfR-free (OffersOnly-Prefix (λ _ → λ ()) (λ _ → OffersOnly-Skip)) tt

    -- the body-offer branch: an EB body
    offB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
             (apiLP l d lnpRecvBlockOffer ⟶ fetchBody n l d)
    offB = wfR-free (OffersOnly-Prefix (λ _ → λ ()) (oo-fetchBody n l d)) tt

    -- the tx-closure branch: transactions
    txB : ∀ {s} → WfR fullα s (λ _ _ → ⊤)
            (apiLP l d lnpRecvBlockTxsOffer ⟶ fetchTxs n l d)
    txB = wfR-free (OffersOnly-Prefix (λ _ → λ ())
                     (λ q → oo↓ (oo-fetchTxs n l d q))) tt

    -- the votes branch: vote blobs
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
  -- THE TWO CONTENT-BEARING LEAVES
  --
  -- The only two threads that ever deposit a ranking block.  Each reaches its deposit
  -- through a chain whose EARLIER step minted the very hash the deposit needs — a gate
  -- that opens in the middle of a loop body, which is what `wfR-Prefix`/`wfR-Output`/
  -- `wf-loop0` are for and what a state-independent alphabet cannot express.
  ------------------------------------------------------------------------

  -- the deposit of a block, under the premise that its certificate hash is already minted
  dep-put : ∀ {s} n (b : Block)
          → (∀ {r} → rbCert b ≡ just r → memberOf r s ≡ true)
          → WfR fullα s (λ _ _ → ⊤) (putEv n ! b ⟶ Skip {0ℓ})
  dep-put n b h = wfR-Output (λ le _ → λ c → memberOf-mono le (h c))
                             (λ _ _ → wfR-free OffersOnly-Skip tt)

  -- THE RENDEZVOUS MINTED EXACTLY THE HASH the block's certificate names.  The list is
  -- pinned explicitly: `memberOf` unfolds to a `foldr` over a `map` and an unpinned
  -- application leaves an uninvertible meta (Task 9's measured trap).
  mint-cert : ∀ {r r′} (s : Minted) → _≡_ {A = Maybe RbHash} (just r) (just r′)
            → memberOf r′ (r ∷ s) ≡ true
  mint-cert {r} s refl = ∈→memberOf r (r ∷ s) (here refl)

  -- THE CERTIFICATE-RB FORGE THREAD — the whole content of S4.  For a block with
  -- `rbCert b = just r` the thread BLOCKS at `hasCertEv n r`, which MINTS `r`, before its
  -- `putEv n ! b`; for a certificate-free block it offers nothing at all.  (`forgeL` is
  -- vacuous BECAUSE of `acceptForgeL`: its only store interaction is `forgeEv`, and the
  -- certificate-carrying case is dropped by the block store, so `forgeL` never fires
  -- `stPut` — that is the reason this theorem is true rather than merely stated.)
  wf-forgeCert : ∀ {ms} n → Wf fullα ms (forgeCert n)
  wf-forgeCert n = wf-loop0 (wfR-Prefix (λ _ _ _ → λ ()) (λ _ b _ → pass b))
    where
    -- one pass, dispatched on the block's optional certificate (passed explicitly, so no
    -- `with` has to abstract the premise that mentions it)
    body : ∀ {s} (b : Block) (z : Maybe RbHash) → rbCert b ≡ z
         → WfR fullα s (λ _ _ → ⊤)
             (maybe′ (λ r → hasCertEv n r ⟶₀ (putEv n ! b ⟶ Skip {0ℓ}))
                     (Skip {0ℓ}) z)
    body b nothing  eq = wfR-free OffersOnly-Skip tt
    body b (just r) eq =
      wfR-Prefix (λ _ _ _ → λ ())
                 (λ {s′} _ _ _ → dep-put n b (λ c → mint-cert s′ (trans (sym eq) c)))

    -- one pass, at the state the `envForgeCert` event led to (it mints nothing)
    pass : ∀ {s} (b : Block)
         → WfR fullα (certRbNext (lbl (forgeCertEv n) b) s) (λ _ _ → ⊤)
             (maybe′ (λ r → hasCertEv n r ⟶₀ (putEv n ! b ⟶ Skip {0ℓ}))
                     (Skip {0ℓ}) (rbCert b))
    pass b = body b (rbCert b) refl

  -- THE WIRE MINT: a BlockFetch delivery of `b` puts `rbCert b`'s hash at the head of the
  -- minted set, so the deposit one step later finds it there.  This is the clause that
  -- makes the WIRE ROUTE unconstrained — deliberately, per the forge-route scope.
  mint-recv : ∀ (z : Maybe RbHash) (s : Minted) {r} → z ≡ just r
            → memberOf r (maybe′ (λ r′ → r′ ∷ []) [] z ++ s) ≡ true
  mint-recv (just r) s refl = ∈→memberOf r (r ∷ s) (here refl)
  mint-recv nothing  s ()

  -- THE BLOCKFETCH CLIENT.  `NodeLogic.clientBody-k` deposits exactly the block that
  -- arrived on `recvBFBlock`, and that delivery MINTED the hash its certificate names.
  -- The node relays; it does not invent.
  wf-clientLoop : ∀ {ms} n ld → Wf fullα ms (clientLoop n ld)
  wf-clientLoop n (l , d) =
    wf-loop0 (wfR-Prefix (λ _ _ _ → λ ())
               (λ _ _ _ → wfR-Prefix (λ _ _ _ → λ ()) (λ _ a _ → k a)))
    where
    -- the reaction to one header: request the block's range, receive it — the mint — and
    -- deposit it.  The `(header b , _)` pattern is what makes `clientBody-k` reduce.
    k : ∀ {s} a → WfR fullα s (λ _ _ → ⊤) (clientBody-k n l d a)
    k (header b , _) =
      wfR-Output (λ _ _ → λ ())
        (λ _ _ → wfR-Prefix (λ _ _ _ → λ ())
                   (λ {s′} _ b′ _ → dep-put n b′ (λ c → mint-recv (rbCert b′) s′ c)))

  ------------------------------------------------------------------------
  -- The assembly
  ------------------------------------------------------------------------

  -- one endpoint's ten threads
  wf-endpoint : ∀ {ms} n e → Wf fullα ms (endpointThreadsL n e)
  wf-endpoint n e =
    wf-⦀ (wf-clientLoop n e)
      (wf-⦀ (wf-nP (oo-serverLoopL n e))
      (wf-⦀ (wf-lnClient n e)
      (wf-⦀ (wf-nP (oo-lnServerLoopL n e))
      (wf-⦀ (wf-nP (oo-bodyOfferLoop n e))
      (wf-⦀ (wf-nP (oo-voteOfferLoop n e))
      (wf-⦀ (wf-nP (oo-ebServeLoop n e))
      (wf-⦀ (wf-nP (oo-ebTxsServeLoop n e))
      (wf-⦀ (wf-nP (oo-tsPull n e)) (wf-nP (oo-tsServe n e))))))))))

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
    wf-⦀ (wf-free (oo-forgeL n))
      (wf-⦀ (wf-forgeCert n)
      (wf-⦀ (wf-nP (oo-ebIndex n))
      (wf-⦀ (wf-nP (oo-voter n))
      (wf-⦀ (wf-nP (oo-submit n))
      (wf-⦀ (wf-nP (oo-certSink n)) (wf-allThreads n))))))

  -- A GATE-CARRYING THREAD GROUP AGAINST ANY STORE GROUP.  The threads carry the gate,
  -- the stores guarantee nothing, and the one key-needing channel is inside `storeES`, so
  -- `Sep` asks the stores for nothing.  Stated for an ARBITRARY thread and store operand
  -- so that the negative control's reduced composite uses the same lemma.
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

  -- S4 — CERTIFICATE-RB ORIGIN, node-local, FORGE-ROUTE SCOPED.  A node running
  -- `nodeLogicL` from empty stores never puts a certificate-carrying ranking block into
  -- its own store unless its own vote store had certified that RB, or the block arrived
  -- off the wire.  LEVEL: node.  The network-wide form ("every certificate RB anywhere
  -- entered through some node's `forgeCert` after that node's `stCert`") needs the medium
  -- and is NOT proved here; see the module header for the full list of what this does not
  -- rule out, and for the reachability finding.
  CertRbSound : Set₁
  CertRbSound = ∀ (n : Node) → CertRbSpecT ⊑T nodeP n (nodeLogicL n st₀)

  -- S4 FOR ANY LOGIC THAT CARRIES THE GATE AND NEVER RETURNS, INSIDE THE BUNDLE.  The
  -- bundle and the logic compose on `apiES` at the full guarantee alphabet (`Sep apiES`
  -- is trivial there), and `wf→osafe` then `osafe→⊑T` turn that one `Wf` fact into the
  -- trace refinement.
  soundOf : ∀ n (lg : Proc) → Wf fullα [] lg → NoRet lg → CertRbSpecT ⊑T nodeP n lg
  soundOf n lg w nr =
    osafe→⊑T (wf→osafe (wf-mono-G (λ _ _ _ → inj₁ tt)
                         (wf-Par apiES sep-api (wf-linkBundlesP n) w))
                       (NoRet-ParR apiES nr))

  -- … and the same WITHOUT the peer bundle, for a composite stated at the threads alone.
  -- This is the load-bearing half of `soundOf`: the bundle contributes only
  -- `wf-linkBundlesP`, which is vacuous (no peer offers a `store` channel).
  soundLogic : ∀ (lg : Proc) → Wf fullα [] lg → NoRet lg → CertRbSpecT ⊑T lg
  soundLogic lg w nr = osafe→⊑T (wf→osafe w nr)

  -- S4, PROVED, at the shipped node logic from empty stores
  certRbSound : CertRbSound
  certRbSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)

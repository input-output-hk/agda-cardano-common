{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE LINEAR-LEIOS NODE LOGIC, `nodeLogicL`.
--
-- An ADDITIVE layer over `Parametric.NodeLogic`: transactions diffuse
-- through TxSubmission, a ranking block announces an endorser block whose
-- body diffuses through LeiosNotify/LeiosFetch, nodes vote on EBs and vote
-- blobs diffuse the same way, and an EB becomes certified or not.
--
-- NOTHING IN `NodeLogic.agda` IS TOUCHED.  `forgeEv`/`putEv`/`getEv`/
-- `offerHeld`/`acceptForge`/`storeES`/`clientLoop`/`serverBody-k` are
-- IMPORTED from it and reused verbatim, exactly as `AnnounceBadLogic` does,
-- so the fourteen announcement-safety and provenance modules are unaffected.
-- The block store is re-formed here as `blockStoreL` (the three original
-- branches plus the read-pointer menu); `NodeLogic.blockStore` itself stays
-- byte-identical and keeps serving `nodeLogic`.
--
-- DESIGN LAW L — READ-POINTER SERVERS.  Every server thread serves each item
-- at most once per endpoint: it carries a pointer `k` through `loop` (not
-- `loop0`) and reads the k-th item through a store event the store offers
-- ONLY while such an item exists.  With nothing new the server BLOCKS at the
-- store, hence the client waiting on it blocks, hence quiescence.  This is
-- what kills the chatter divergence of `nodeLogic` (`Negative/Chatter.agda`).
--
-- INDICES COUNT FROM THE OLDEST END.  `NodeLogic.blockStore` PREPENDS
-- (`b ∷ held`), so `blockStoreL` enumerates `reverse held`; the four stores
-- introduced here APPEND (`insertU`), so they enumerate themselves.  Either
-- way index `k` never shifts under a later deposit.
--
-- SYNC-PARTNER RULE — AND ITS POLARITY.  `storeES` is a synchronisation set
-- (`NodeLogic.storeSet`: EVERY `store` channel AND EVERY `env` channel), so an
-- event in it fires only when BOTH sides offer it.  THE RULE IS SYMMETRIC, and
-- an earlier version of this paragraph got that wrong by listing only one
-- polarity: a store-side event with no thread-side partner blocks that STORE
-- forever (`stCert` needs `certSink`), and a THREAD-side event with no
-- store-side partner blocks that THREAD forever (`envForgeCert` needs an arm
-- in `storeStepL`, `envSubmit` one in `memStep`).  The inverted pair is the
-- easy one to miss precisely because an `env` channel reads like an input from
-- outside the node — but `storeSet` puts it in the rendezvous set all the
-- same, so the environment can only reach a thread THROUGH a store.
-- The four pairs, each named with the side that would otherwise be alone:
--   `envForge`     — thread `forgeL`     / store `storeStepL`
--   `envForgeCert` — thread `forgeCert`  / store `storeStepL`  (the second arm)
--   `envSubmit`    — thread `submit`     / store `memStep`     (the second arm)
--   `stCert`       — store `voteStep`    / thread `certSink`
-- The two `env*Cert`/`envSubmit` store arms were MISSING as originally shipped,
-- which blocked `forgeCert` and `submit` at their first event; they are present
-- now and both threads are live (`Leios/NodeLogicLSanity.agda` witnesses each
-- first step inside the full `nodeLogicL`).
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Leios.NodeLogicL where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.List using (List; []; _∷_; map; reverse; _++_)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U
open import Level using (0ℓ)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI
open import Class.DecEq.Instances using (DecEq-List)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; opposite)
import CSP.Examples.Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL

-- the Linear-Leios logic, parametric in the network parameters, the Leios parameters,
-- the topology, the api alphabet and the node-to-voter map.  `voterOf` is a parameter
-- here and not a `LeiosParams` field because it needs `Topology`'s `Node`; instances
-- take `VoterId := Node` and `voterOf := id`.
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open Params p using (Block; LSlot; VoterId; VoteBlob; EB; EBHash; RbHash; Tx; TxHash; Size
                      ; ebHash; rbHash; txHash; slotOf; announcedEB
                      ; decBlock; decEBHash; decLSlot; decVoteBlob; decEB
                      ; decRbHash; decTx; decTxHash)
  -- `LeiosEb`/`LeiosPoint`, their `DecEq` instance and the derived all-offsets request
  -- live in `LeiosParams.agda`, not redefined here
  open LeiosP p using (LeiosEb; LeiosPoint; DecEq-LeiosPoint; allOffsets)
  open LeiosP.LeiosParams lp using (mkVoteBlob; blobVoter; blobRb; certifies; ebTxs
                                   ; ebSize; rbCert)
  open import CSP.Examples.Cardano_network.Base using (Dir)
  -- EVERY tag this module names MUST appear here: an unlisted tag silently becomes a
  -- pattern VARIABLE and the carrier table turns into a stuck term (ledger gotcha 1).
  open N p
    using ( Link; Net_Api; Net_Api-≟; apiCS; apiTS; apiLP; store; env
          ; stPut; stGet; stGetAt; stPutEB; stGetEBAt; stPutBody; stGetBody
          ; stPutTx; stGetTxAt; stGetTx; stPutVote; stGetVoteAt; stCert; stHasCert
          ; envForge; envSubmit; envForgeCert
          ; reqCSRequestNext; sendCSRequestNext; recvCSRollforward
          ; lnpSendRequestNext; lnpSendBlockAnnouncement; lnpSendBlockOffer
          ; lnpSendBlockTxsOffer; lnpSendVotes
          ; lnpRecvBlockAnnouncement; lnpRecvBlockOffer; lnpRecvBlockTxsOffer
          ; lnpRecvVotes
          ; lfpSendBlockRequest; lfpSendBlockTxsRequest; lfpSendBlock; lfpSendBlockTxs
          ; lfpRecvBlock; lfpRecvBlockTxs
          ; lfpReqBlockRequest; lfpReqBlockTxsRequest
          ; sendTSRequestTxIdsBlocking; sendTSRequestTxsPipelined
          ; recvTSReplyTxIds; recvTSReplyTxs
          ; recvTSRequestTxIds; recvTSRequestTxs
          ; sendTSReplyTxIds; sendTSReplyTxs )
  -- `Tx`/`TxHash` come from `Params` (`Data` does not re-export them and `txData` is
  -- gone); every `Output` on an `apiLP` channel names one of these DecEq TERMS rather than
  -- relying on instance search, so a later proof analysing that `Output` sees the same term.
  open D p
    using ( Payload; Header; header; TxBitmap
          ; DecEq-Header; DecEq-EBPoint; DecEq-TxBitmap; DecEq-TxEntries
          ; DecEq-TxsRequest; DecEq-TxsReply; DecEq-Offer )
  open Topology t using (Node; endpointsOf)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using ( EventSet; _∥⇘_⇙_; _⦀_; ⦀⁺; _□_; _◁_▷_; _>>_
          ; Skip; Stop; Ret; Prefix; Prefix₀; Output; loop; loop0 )
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES using (Proc)
  open NL.Generic p t apiES
    using ( Held; StoreProc; homeOf; forgeEv; putEv; getEv; offerHeld; acceptForge
          ; storeES; clientLoop; serverBody-k )

  instance
    -- the `DecEq (⊤ {0ℓ})` the `□`s at `Proc` level need (the `VendingMachine` idiom)
    DecEq-⊤poly : DecEq (⊤ {0ℓ})
    DecEq-⊤poly = record { _≟_ = λ _ _ → yes refl }

    -- the vote-store state: the blobs held, paired with the RB hashes already certified
    DecEq-Votes : DecEq (List VoteBlob × List RbHash)
    DecEq-Votes = DecEqI.DecEq-×

  ------------------------------------------------------------------------
  -- State and channel abbreviations, and the two shared helpers
  ------------------------------------------------------------------------

  -- the EB entries a node knows from RB headers: an EB hash and the slot of the RB
  -- that announced it
  Entries : Set
  Entries = List LeiosPoint

  -- the EB bodies a node holds
  Bodies : Set
  Bodies = List LeiosEb

  -- a node's mempool
  Mem : Set
  Mem = List Tx

  -- the vote blobs a node holds
  Blobs : Set
  Blobs = List VoteBlob

  -- the RB hashes a node has already issued a certificate for
  Certs : Set
  Certs = List RbHash

  -- the vote store's state: the blobs, and the RB hashes already certified
  Votes : Set
  Votes = Blobs × Certs

  -- a node's whole local state
  StateL : Set
  StateL = Held × Entries × Bodies × Mem × Votes

  -- every store of a fresh node is empty
  st₀ : StateL
  st₀ = [] , [] , [] , [] , ([] , [])

  -- the k-th-oldest-block channel of `n` (design law L: `blockStoreL` offers it only
  -- while a k-th oldest block exists)
  getAtEv : Node → ℕ → Net_Api Payload Block
  getAtEv n k = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) (stGetAt k)

  -- the EB-entry deposit channel of `n`
  putEBEv : Node → Net_Api Payload LeiosPoint
  putEBEv n = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) stPutEB

  -- the k-th-oldest-EB-entry channel of `n`
  getEBAtEv : Node → ℕ → Net_Api Payload LeiosPoint
  getEBAtEv n k = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) (stGetEBAt k)

  -- the EB-body deposit channel of `n`
  putBodyEv : Node → Net_Api Payload LeiosEb
  putBodyEv n = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) stPutBody

  -- the body-by-hash channel of `n`: offered iff the node holds that body, so this
  -- synchronisation IS the "do not vote on a body you have not seen" guard
  getBodyEv : Node → EBHash → Net_Api Payload LeiosEb
  getBodyEv n h = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) (stGetBody h)

  -- the mempool deposit channel of `n`
  putTxEv : Node → Net_Api Payload Tx
  putTxEv n = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) stPutTx

  -- the k-th-oldest-mempool-transaction channel of `n`
  getTxAtEv : Node → ℕ → Net_Api Payload Tx
  getTxAtEv n k = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) (stGetTxAt k)

  -- the vote-blob deposit channel of `n`
  putVoteEv : Node → Net_Api Payload VoteBlob
  putVoteEv n = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) stPutVote

  -- the k-th-oldest-vote-blob channel of `n`
  getVoteAtEv : Node → ℕ → Net_Api Payload VoteBlob
  getVoteAtEv n k = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) (stGetVoteAt k)

  -- the certificate channel of `n`: fired once per RANKING BLOCK, by the vote store
  certEv : Node → Net_Api Payload RbHash
  certEv n = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) stCert

  -- the "is this RB already certified here?" channel of `n`: offered by the vote store
  -- exactly for the RB hashes in its `certs` list, so synchronising on it IS the guard
  -- `forgeCert` needs.  Its carrier is `Net.StoreCar (stHasCert r)`, i.e. the NON-
  -- polymorphic `Data.Unit.⊤` that `Net.agda` uses.
  hasCertEv : Node → RbHash → Net_Api Payload U.⊤
  hasCertEv n r = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) (stHasCert r)

  -- the certificate-RB forge channel of `n`: the environment offers a ranking block whose
  -- body carries a certificate
  forgeCertEv : Node → Net_Api Payload Block
  forgeCertEv n = env (proj₁ (homeOf n)) (proj₂ (homeOf n)) envForgeCert

  -- the transaction-BY-HASH channel of `n`: offered iff the mempool holds a transaction
  -- with that hash.  The `stGetBody h` idiom on the mempool — the store-side lookup that
  -- makes a served tx-closure entry real.
  getTxEv : Node → TxHash → Net_Api Payload Tx
  getTxEv n h = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) (stGetTx h)

  -- the transaction-submission channel of `n`: the environment injects a fresh tx
  submitEv : Node → Net_Api Payload Tx
  submitEv n = env (proj₁ (homeOf n)) (proj₂ (homeOf n)) envSubmit

  -- the `k`-th element of a list, or `nothing` past the end.  The stdlib's `lookup` needs a
  -- `Fin (length xs)`; a tx-bitmap offset is a plain `ℕ` that may miss.
  at? : ∀ {A : Set} → ℕ → List A → Maybe A
  at? _       []       = nothing
  at? zero    (x ∷ _)  = just x
  at? (suc k) (_ ∷ xs) = at? k xs

  -- is `x` already in `xs`?
  memberOf : ∀ {A : Set} → ⦃ DecEq A ⦄ → A → List A → Bool
  memberOf x xs = any (λ y → ⌊ y ≟ x ⌋) xs

  -- DEDUP INSERT at the YOUNGEST end.  Every store is a list-as-set, so `Unique` is an
  -- invariant and `length` is a genuine cardinality; appending keeps the enumeration
  -- oldest-first, so a read pointer never shifts under a later deposit.
  insertU : ∀ {A : Set} → ⦃ DecEq A ⦄ → A → List A → List A
  insertU x xs = if memberOf x xs then xs else xs ++ (x ∷ [])

  -- THE READ-POINTER MENU of law L: offer `e k ! x` for the k-th item of the
  -- oldest-first list `xs`, leaving the store state `s` intact.  Nothing is offered
  -- past the last item, so a server whose pointer has caught up BLOCKS at the store.
  offerIx : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {S : Set} ⦃ _ : DecEq S ⦄
          → (ℕ → Net_Api Payload A) → List A → ℕ → S
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) S
  offerIx e []       k s = Stop
  offerIx e (x ∷ xs) k s = (e k ! x ⟶ Ret s) □ offerIx e xs (suc k) s

  ------------------------------------------------------------------------
  -- The five stores
  ------------------------------------------------------------------------

  -- `acceptForge` RESTRICTED TO CERTIFICATE-FREE BLOCKS.  An `envForge` of a block with
  -- `rbCert b = just r` still fires — the forge loop keeps its visible event — but the
  -- store is left unchanged, so a certificate RB cannot be LOCALLY FORGED into `held`: the
  -- forge route for such a block is `forgeCert`'s `putEv`, taken only after the
  -- `stHasCert r` rendezvous.  `NodeLogic.acceptForge` itself is NOT edited.
  --
  -- THE SCOPE OF S4 (spec §5.4).  S4 is a FORGE-ROUTE statement: every cert-RB that enters
  -- `held` BY THE FORGE ROUTE was preceded by a local `stCert` for the RB its `rbCert`
  -- names.  It is NOT a statement about `held` as a whole.  `storeStepL`'s `putEv` branch
  -- below is UNGATED, and `NodeLogic.clientBody-k` deposits through it any block received
  -- off the wire, cert-carrying or not — which spec §4.5 requires, a cert-RB "diffuses
  -- like any RB".  That wire route is DELIBERATELY ungated, exactly as S1/S2 already found
  -- for their channels: a node accepts what a peer sends it, and provenance for the wire
  -- route is the origin theorems' business, not S4's.  Tasks 8-10 must quote S4 with this
  -- scope and never as "only `forgeCert` can put a cert-RB in `held`".
  acceptForgeL : Maybe LeiosEb × Block → Held → Held
  acceptForgeL (me , b) held with rbCert b
  ... | just _  = held
  ... | nothing = acceptForge (me , b) held

  -- one step of the RB store: `NodeLogic.storeStep`'s three branches (with `acceptForge`
  -- replaced by `acceptForgeL` in the forge branch), plus the read-pointer menu law L
  -- needs.  `held` is PREPENDED by the put/forge branches, so the menu enumerates
  -- `reverse held`.  The `putEv` branch is UNGATED — see the S4 scope note above.
  --
  -- THE `envForgeCert` ARM — the store side `forgeCert` was missing — is a PURE
  -- RENDEZVOUS: it leaves `held` UNCHANGED.  That is the design, not an omission:
  -- `acceptForgeL` rejects a cert-carrying RB on the `envForge` route and this arm
  -- deposits nothing, so the ONLY way a certificate RB reaches `held` is `forgeCert`'s
  -- own `putEv`, taken after the `stHasCert r` rendezvous.  Without the arm the thread
  -- could not fire even its first event (SYNC-PARTNER RULE, module header).
  storeStepL : Node → Held → StoreProc
  storeStepL n held =
      (forgeEv n ⟶ (λ mb → Ret (acceptForgeL mb held)))
    □ ((forgeCertEv n ⟶ (λ _ → Ret held))
    □ ((putEv n ⟶ (λ b → Ret (b ∷ held)))
    □ (offerHeld n held held
    □  offerIx (getAtEv n) (reverse held) 0 held)))

  -- the node's RB store holding `held`: `NodeLogic.blockStore`'s loop over the extended
  -- step.  `NodeLogic.blockStore` itself is untouched and still serves `nodeLogic`.
  blockStoreL : Node → Held → Proc
  blockStoreL n held = loop (storeStepL n) held

  -- one step of the EB-entry store: deposit an `(EB hash , announcing slot)` pair with a
  -- dedup insert, or hand over the k-th oldest entry
  ebStep : Node → Entries → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Entries
  ebStep n es =
      (putEBEv n ⟶ (λ e → Ret (insertU e es)))
    □  offerIx (getEBAtEv n) es 0 es

  -- the node's EB-entry store.  KEPT as the node's "EBs known from headers" table, but
  -- NO THREAD READS IT any more: the voter walks `held` (spec §4.4), so `ebIndex` fills
  -- this store and nothing consumes it.
  ebStore : Node → Entries → Proc
  ebStore n es = loop (ebStep n) es

  -- one step of the EB-body store: deposit a body unless its hash is already held, or
  -- hand over the body with a given hash.  A body is keyed by its hash, so this store
  -- needs no pointer and may serve the same body any number of times.  (Forward
  -- declaration: `bodyStep` calls `offerBodies`, defined right after it.)
  bodyStep : Node → Bodies → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies
  offerBodies : Node → Bodies → Bodies
              → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies

  bodyStep n bs =
      (putBodyEv n ⟶ (λ eb → Ret (if memberOf (ebHash eb) (map ebHash bs)
                                   then bs else bs ++ (eb ∷ []))))
    □  offerBodies n bs bs

  -- offer `stGetBody (ebHash eb) ! eb` for every body held, leaving the state intact
  offerBodies n bs []         = Stop
  offerBodies n bs (eb ∷ ebs) = (getBodyEv n (ebHash eb) ! eb ⟶ Ret bs) □ offerBodies n bs ebs

  -- the node's EB-body store
  bodyStore : Node → Bodies → Proc
  bodyStore n bs = loop (bodyStep n) bs

  -- DEDUP ON THE KEY: a transaction is identified by its hash, so the mempool keeps at most
  -- one transaction per `txHash` — the table `txHash ↦ tx` of the ADR.  The `bodyStep`
  -- idiom, on `txHash` instead of `ebHash`.
  insertTx : Tx → Mem → Mem
  insertTx tx ts = if memberOf (txHash tx) (map txHash ts) then ts else ts ++ (tx ∷ [])

  -- one step of the mempool: key-dedup-insert a transaction, THE STORE SIDE OF
  -- `envSubmit`, hand over the k-th oldest (the TxSubmission server's read pointer), or
  -- hand over the one with a given hash (the tx-closure server's keyed lookup).
  -- Forward declaration: `memStep` calls `offerTxs`, defined right after it.
  --
  -- THE `envSubmit` ARM — the store side `submit` was missing — is a PURE RENDEZVOUS:
  -- it leaves `ts` UNCHANGED, and the transaction reaches the mempool through
  -- `submit`'s own following `stPutTx`, the same deposit channel every wire route uses.
  -- The `Tx`-OPAQUE DISCIPLINE survives: the arm is an INPUT, so the transaction is the
  -- environment's own value handed over whole — nothing here manufactures a `Tx`, and
  -- in particular nothing rebuilds one from a `TxHash`.
  memStep : Node → Mem → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Mem
  offerTxs : Node → Mem → Mem → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Mem

  memStep n ts =
      (putTxEv n ⟶ (λ tx → Ret (insertTx tx ts)))
    □ ((submitEv n ⟶ (λ _ → Ret ts))
    □ ((offerIx (getTxAtEv n) ts 0 ts)
    □   offerTxs n ts ts))

  -- offer `stGetTx (txHash tx) ! tx` for every transaction held, leaving the state intact
  offerTxs n ts []         = Stop
  offerTxs n ts (tx ∷ txs) = (getTxEv n (txHash tx) ! tx ⟶ Ret ts) □ offerTxs n ts txs

  -- the node's mempool
  mempool : Node → Mem → Proc
  mempool n ts = loop (memStep n) ts

  -- fire the certificate for `r` exactly once: only when the oracle now certifies `r`
  -- against the blobs held AND no certificate for `r` has been issued yet
  certify : Node → Blobs → Certs → RbHash
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Votes
  certify n bs cs r =
    (certEv n ! r ⟶ Ret (bs , r ∷ cs))
      ◁ (certifies bs r ∧ not (memberOf r cs)) ▷
    Ret (bs , cs)

  -- offer `stHasCert r` for every RB hash already certified, state intact.  This is the
  -- store side of `forgeCert`'s guard: nothing is offered for an uncertified RB, so
  -- `forgeCert` BLOCKS there — design law L applied to a membership test.  The channel is
  -- value-free, so both sides use `⟶₀` (`Prefix₀`) and no `DecEq ⊤` is needed.
  offerCerts : Node → Votes → Certs
             → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Votes
  offerCerts n vs []       = Stop
  offerCerts n vs (r ∷ rs) = (hasCertEv n r ⟶₀ Ret vs) □ offerCerts n vs rs

  -- one step of the vote store: dedup-insert a blob and consult the certification oracle,
  -- hand over the k-th oldest blob, or answer a certificate query.  `stCert` needs a
  -- thread partner (`certSink`) because `storeES` is a synchronisation set.
  voteStep : Node → Votes → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Votes
  voteStep n (bs , cs) =
      (putVoteEv n ⟶ (λ v → certify n (insertU v bs) cs (blobRb v)))
    □ ((offerIx (getVoteAtEv n) bs 0 (bs , cs))
    □   offerCerts n (bs , cs) cs)

  -- the node's vote store
  voteStore : Node → Votes → Proc
  voteStore n vs = loop (voteStep n) vs

  ------------------------------------------------------------------------
  -- The six node-level threads
  ------------------------------------------------------------------------

  -- THE FORGE GUARD as a Boolean: exactly the test `NodeLogic.acceptForge` performs
  -- (`announcedEB b ≡ (ebHash <$> me)`), so a body is deposited only for a forge the
  -- block store also accepts.  A pure test — no cross-store read.
  forgeOK : Maybe LeiosEb × Block → Bool
  forgeOK (me , b) = ⌊ announcedEB b ≟ Data.Maybe.map ebHash me ⌋

  -- the body deposited by one forge: the forged EB, when the forge is accepted
  forgeBodyL : Node → Maybe LeiosEb × Block → Proc
  forgeBodyL n (me , b) =
    (maybe (λ eb → putBodyEv n ! eb ⟶ Skip) Skip me) ◁ forgeOK (me , b) ▷ Skip

  -- THE FORGE THREAD: fire the environment's forge, and deposit the forged EB body
  -- when the forge is accepted.  It is also the sync partner `envForge` needs.
  -- VISIBLE EVENT PER PASS: `env home(n) envForge`.
  forgeL : Node → Proc
  forgeL n = loop0 (forgeEv n ⟶ forgeBodyL n)

  -- THE CERTIFICATE-RB FORGE THREAD: the environment offers a ranking block; if its body
  -- carries a certificate for `r`, the block enters `held` only AFTER the vote store has
  -- certified `r` (the `stHasCert r` rendezvous).  A certificate-free block offered here is
  -- simply dropped — `forgeL`/`envForge` is its route.
  -- VISIBLE EVENT PER PASS: `env home(n) envForgeCert`.
  -- POLARITY — THIS THREAD IS THE **THREAD** SIDE, NOT "the sync partner `envForgeCert`
  -- needs".  Every `env` channel is in `storeES` (`NodeLogic.storeSet`) and a
  -- synchronised event fires only when BOTH operands of `∥⇘ storeES ⇙` offer it, so this
  -- thread needs a STORE-side arm, which `storeStepL` now supplies.  It was missing as
  -- originally shipped and the whole thread was blocked at its first event; it is live
  -- now, witnessed inside the full `nodeLogicL` by
  -- `Leios/NodeLogicLSanity.forgeCert-first-step`.  The SECOND event stays gated: from
  -- empty stores no `stHasCert r` is offered, so a cert-RB is deposited only after this
  -- node has certified `r` — that gate is what S4 proves and `CertRbOriginBad` refutes
  -- without it.
  forgeCert : Node → Proc
  forgeCert n =
    loop0 (forgeCertEv n ⟶ (λ b →
      maybe′ (λ r → hasCertEv n r ⟶₀ (putEv n ! b ⟶ Skip)) Skip (rbCert b)))

  -- one pass of the EB index: take the k-th oldest held RB and, when it announces an
  -- EB, record `(hash , announcing slot)` in the EB store.  Purely additive — the
  -- ChainSync client is untouched and the entry is derived from a header already
  -- stored.
  ebIndexBody : Node → ℕ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ
  ebIndexBody n k =
    getAtEv n k ⟶ (λ b →
      maybe′ (λ h → putEBEv n ! (h , slotOf b) ⟶ Ret (suc k))
             (Ret (suc k))
             (announcedEB b))

  -- THE EB INDEX THREAD: a read pointer over `held`, forever
  ebIndex : Node → Proc
  ebIndex n = loop (ebIndexBody n) 0

  -- THE VOTING THREAD'S BODY: read the k-th oldest HELD ranking block, and if it announces
  -- an EB, BLOCK at that EB's body before casting a vote naming the RB.  "I vote for `b`"
  -- therefore means "I hold `b` and the body it announces" — the prototype has no
  -- projection from a blob to an EB and neither does this model.  (It walks `held`, not
  -- `ebStore`, which is why `ebStore` now has no reader.)
  voterBody : Node → ℕ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ
  voterBody n k =
    getAtEv n k ⟶ (λ b →
      maybe′ (λ h → getBodyEv n h ⟶ (λ _ →
                      putVoteEv n ! mkVoteBlob (voterOf n) (rbHash b) ⟶ Ret (suc k)))
             (Ret (suc k))
             (announcedEB b))

  -- THE VOTING THREAD: a read pointer over the RB store, forever
  voter : Node → Proc
  voter n = loop (voterBody n) 0

  -- THE SUBMISSION THREAD: accept a transaction from the environment and put it in the
  -- mempool.
  -- POLARITY — THIS THREAD IS THE **THREAD** SIDE, NOT "the sync partner `envSubmit`
  -- needs", exactly as `forgeCert` above.  `envSubmit` is in `storeES`, so the thread
  -- needs a STORE-side arm, which `memStep` now supplies; without it the thread was
  -- blocked at its first event and the node had NO ENVIRONMENT ROUTE INTO ITS MEMPOOL at
  -- all.  It is live now, witnessed inside the full `nodeLogicL` by
  -- `Leios/NodeLogicLSanity.submit-first-step`, and it joins the two wire routes
  -- (`putChecked`, a tx-closure reply, and `putAllTx`, a TxSubmission pull).
  submit : Node → Proc
  submit n = loop0 (submitEv n ⟶ (λ tx → putTxEv n ! tx ⟶ Skip))

  -- THE CERTIFICATE SINK: absorb the vote store's `stCert`.  Without it `stCert` has no
  -- partner in `storeES` and the vote store would block forever on the first
  -- certification.
  certSink : Node → Proc
  certSink n = loop0 (certEv n ⟶ (λ _ → Skip))

  ------------------------------------------------------------------------
  -- The per-endpoint threads
  --
  -- DIRECTION RULE.  `Node.bundleAt (l , d) = nodeBundle l d (opposite d)`
  -- puts a node's CLIENT peers at `d` and its SERVER peers at `opposite d`.
  -- So a thread talking to a client peer drives `d`, one talking to a server
  -- peer drives `opposite d`.  TxSubmission inverts the roles: its SUBMITTER
  -- is the protocol's `clientStep` (a CLIENT peer, hence `d`) and its
  -- REQUESTER is `serverStep` (a SERVER peer, hence `opposite d`).
  ------------------------------------------------------------------------

  instance
    -- the `sendTSRequestTxIdsBlocking` carrier (ack-count × request-count)
    DecEq-ℕ×ℕ : DecEq (ℕ × ℕ)
    DecEq-ℕ×ℕ = DecEqI.DecEq-× ⦃ DecEqI.DecEq-ℕ ⦄ ⦃ DecEqI.DecEq-ℕ ⦄

  -- one server round with a READ POINTER (law L): await the far end's RequestNext,
  -- take the k-th OLDEST held block, announce and serve it via `NodeLogic.serverBody-k`
  -- verbatim, then advance.  Each held block is served once per endpoint — the chatter
  -- of `NodeLogic.serverLoop` (which re-serves from `offerHeld` forever) is gone.
  serverBodyL : Node → Link → Dir → ℕ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ
  serverBodyL n l d k =
    apiCS l d reqCSRequestNext ⟶₀
      (getAtEv n k ⟶ (λ b → serverBody-k n l d b >> Ret (suc k)))

  -- the ChainSync server thread of one endpoint.  IT DRIVES `opposite d`.
  serverLoopL : Node → Link × Dir → Proc
  serverLoopL n (l , d) = loop (serverBodyL n l (opposite d)) 0

  -- one LN announce round with a read pointer: take the k-th oldest held RB and
  -- announce its HEADER.  It announces from `held`, not from the EB store: the LN
  -- message carries a `Header`, and an `(h , s)` entry has none.
  lnServerBodyL : Node → Link → Dir → ℕ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ
  lnServerBodyL n l d k =
    getAtEv n k ⟶ (λ b → apiLP l d lnpSendBlockAnnouncement ! header b ⟶ Ret (suc k))

  -- the LN announce thread of one endpoint.  IT DRIVES `opposite d`.
  lnServerLoopL : Node → Link × Dir → Proc
  lnServerLoopL n (l , d) = loop (lnServerBodyL n l (opposite d)) 0

  -- one body-offer round: take the k-th oldest held RB and, when it announces an EB,
  -- BLOCK until this node holds that body, then offer the POINT AND THE SIZE and, in the
  -- same round, the tx closure of that point (the prototype's `MsgLeiosBlockOffer` +
  -- `MsgLeiosBlockTxsOffer`).  `ebSize` is the `LeiosParams` projection.  A node offers a
  -- body only once it holds it — which is what makes offer-driven fetch wedge-free.
  -- KNOWN CEILING: an RB whose body never arrives holds this pointer up, so later
  -- bodies are not offered on this endpoint.  Deliberate (spec §4.5), not a wedge.
  bodyOfferBody : Node → Link → Dir → ℕ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ
  bodyOfferBody n l d k =
    getAtEv n k ⟶ (λ b →
      maybe′ (λ h → getBodyEv n h ⟶ (λ eb →
                Output ⦃ DecEq-Offer ⦄ (apiLP l d lnpSendBlockOffer)
                  ((h , slotOf b) , ebSize eb)
                  (Output ⦃ DecEq-EBPoint ⦄ (apiLP l d lnpSendBlockTxsOffer)
                     (h , slotOf b) (Ret (suc k)))))
             (Ret (suc k))
             (announcedEB b))

  -- the body-offer thread of one endpoint.  IT DRIVES `opposite d`.
  bodyOfferLoop : Node → Link × Dir → Proc
  bodyOfferLoop n (l , d) = loop (bodyOfferBody n l (opposite d)) 0

  -- one vote-offer round: take the k-th oldest vote blob and send THE BLOB ITSELF, one
  -- per reply (`MsgLeiosVotes [vote]`).  The prototype has no vote fetch, so a vote is
  -- delivered by the notification and never requested.
  voteOfferBody : Node → Link → Dir → ℕ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ
  voteOfferBody n l d k =
    getVoteAtEv n k ⟶ (λ v →
      Output ⦃ DecEqI.DecEq-List ⦄ (apiLP l d lnpSendVotes) (v ∷ []) (Ret (suc k)))

  -- the vote-offer thread of one endpoint.  IT DRIVES `opposite d`.
  voteOfferLoop : Node → Link × Dir → Proc
  voteOfferLoop n (l , d) = loop (voteOfferBody n l (opposite d)) 0

  -- fetch the body that was OFFERED, and store it only if its hash matches the point the
  -- request named — `MsgLFPBlock` carries no point, so the guard is against the REQUESTED
  -- point (spec §2.2, §3 "wire checks").  This is the guard S1 rests on.
  fetchBody : Node → Link → Dir → (EBHash × LSlot) × Size → Proc
  fetchBody n l d (q , _) =
    Output ⦃ DecEq-EBPoint ⦄ (apiLP l d lfpSendBlockRequest) q
      (apiLP l d lfpRecvBlock ⟶ (λ eb →
         (putBodyEv n ! eb ⟶ Skip) ◁ ⌊ ebHash eb ≟ proj₁ q ⌋ ▷ Skip))

  -- DEPOSIT EVERY CHECKED ENTRY of a tx-closure reply: an entry `(o , tx)` is stored only
  -- when `tx` really is the transaction the EB body's table names at offset `o`.  An entry
  -- that fails the check, or whose offset is past the table, is SKIPPED — the reply is
  -- data, and dropping a bad entry is the modelled form of the prototype's wire check.
  -- see ADR 2026-09-21 (leios-tx-closure-and-object-identities)
  putChecked : Node → EBHash → List (ℕ × Tx) → Proc
  putChecked n h []             = Skip
  putChecked n h ((o , tx) ∷ es) with at? o (ebTxs h)
  ... | nothing      = putChecked n h es
  ... | just (k , _) = (putTxEv n ! tx ⟶ putChecked n h es)
                         ◁ ⌊ txHash tx ≟ k ⌋ ▷ putChecked n h es

  -- fetch the WHOLE tx closure of an offered point.  BLOCK first at the body the point
  -- names (a closure without its EB body is meaningless), then request every offset of
  -- that body's table, then check the echoed point and hand the entries to `putChecked`.
  -- The reply does NOT echo the bitmap: the offsets are the entries' keys.
  -- LIVENESS CEILING: that leading `getBodyEv` BLOCKS the ONE Notify client thread when the
  -- body is not held — reachable when `fetchBody`'s hash guard rejected a bad EB, i.e. under
  -- the very threat model S1 addresses — and with it the announcement, offer and vote arms
  -- of this endpoint.  Deliberate (a closure without its body is meaningless), not a wedge
  -- in the C2 sense, but it is a ceiling Task 10 must not mistake for deadlock-freedom.
  fetchTxs : Node → Link → Dir → EBHash × LSlot → Proc
  fetchTxs n l d q =
    getBodyEv n (proj₁ q) ⟶ (λ _ →
      Output ⦃ DecEq-TxsRequest ⦄ (apiLP l d lfpSendBlockTxsRequest)
        (q , allOffsets lp (proj₁ q))
        (apiLP l d lfpRecvBlockTxs ⟶ (λ { (q′ , es) →
           putChecked n (proj₁ q) es ◁ ⌊ DecEq-EBPoint ._≟_ q′ q ⌋ ▷ Skip })))

  -- deposit every delivered vote blob, in order
  putAllVotes : Node → List VoteBlob → Proc
  putAllVotes n []       = Skip
  putAllVotes n (v ∷ vs) = putVoteEv n ! v ⟶ putAllVotes n vs

  -- ONE Notify client round, a four-way `□` after the long-poll request.  Two Notify
  -- clients on one peer would deadlock, so this stays one thread.  THE ANNOUNCEMENT BRANCH
  -- IS A NO-OP (correction C2: a node fetches a body only in response to an OFFER, because
  -- the offerer offers only bodies it holds and bodies are never removed, so the fetch
  -- server can always answer and the head-of-line wedge cannot occur).
  lnClientBodyL : Node → Link → Dir → Proc
  lnClientBodyL n l d =
    apiLP l d lnpSendRequestNext ⟶₀
      ((apiLP l d lnpRecvBlockAnnouncement ⟶ (λ _ → Skip))
      □ ((apiLP l d lnpRecvBlockOffer    ⟶ fetchBody n l d)
      □ ((apiLP l d lnpRecvBlockTxsOffer ⟶ fetchTxs  n l d)
      □  (apiLP l d lnpRecvVotes         ⟶ putAllVotes n))))

  -- the LN client thread of one endpoint.  IT DRIVES `d`.
  lnClientLoopL : Node → Link × Dir → Proc
  lnClientLoopL n (l , d) = loop0 (lnClientBodyL n l d)

  -- one EB-serve round: the LF producer reports the POINT the far end asked for, the body
  -- store hands that body over, and it goes out on the wire.  The far end requests only
  -- points this node OFFERED, and bodies are never removed, so `stGetBody` never blocks in
  -- the good logic.
  ebServeBody : Node → Link → Dir → Proc
  ebServeBody n l d =
    apiLP l d lfpReqBlockRequest ⟶ (λ q →
      getBodyEv n (proj₁ q) ⟶ (λ eb → apiLP l d lfpSendBlock ! eb ⟶ Skip))

  -- the EB-serve thread of one endpoint.  IT DRIVES `opposite d`.
  ebServeLoop : Node → Link × Dir → Proc
  ebServeLoop n (l , d) = loop0 (ebServeBody n l (opposite d))

  -- SERVE THE REQUESTED OFFSETS, then send the offset-indexed reply.  For each offset `o`
  -- the EB body table gives a hash, and `stGetTx` — offered only for a transaction the
  -- mempool HOLDS — gives the transaction; that store read is what makes the reply's
  -- entries real.  An offset past the table is skipped.  Structurally recursive on the
  -- bitmap, so no `>>=` and no corecursion here.
  -- LIVENESS CEILING: `getTxEv n h` BLOCKS when this node holds the EB body but not the
  -- transaction at offset `o` — holding a body does not imply holding its closure.  Because
  -- `ebServeLoop` and `ebTxsServeLoop` drive the SAME LeiosFetchP producer, a round stuck in
  -- `stBlockTxs` also stops EB-BODY serving on this endpoint.  Reachable in the good logic
  -- and sanctioned by spec §5.2 (the store read is exactly what makes the reply's entries
  -- real); skipping a missing hash the way a bad offset is skipped would trade that for
  -- wedge-freedom.  Task 10 / `Negative/FetchWedge` owns the choice.
  -- see ADR 2026-09-21 (leios-tx-closure-and-object-identities)
  serveTxs : Node → Link → Dir → EBHash × LSlot → TxBitmap → List (ℕ × Tx) → Proc
  serveTxs n l d q []       acc =
    Output ⦃ DecEq-TxsReply ⦄ (apiLP l d lfpSendBlockTxs) (q , acc) Skip
  serveTxs n l d q (o ∷ os) acc with at? o (ebTxs (proj₁ q))
  ... | nothing      = serveTxs n l d q os acc
  ... | just (h , _) =
        getTxEv n h ⟶ (λ tx → serveTxs n l d q os (acc ++ ((o , tx) ∷ [])))

  -- one tx-closure-serve round: the LF producer reports the request, the body store
  -- confirms this node holds the EB, and `serveTxs` builds and sends the reply
  ebTxsServeBody : Node → Link → Dir → Proc
  ebTxsServeBody n l d =
    apiLP l d lfpReqBlockTxsRequest ⟶ (λ { (q , bm) →
      getBodyEv n (proj₁ q) ⟶ (λ _ → serveTxs n l d q bm []) })

  -- the tx-closure-serve thread of one endpoint.  IT DRIVES `opposite d`.
  -- see ADR 2026-09-21 (leios-tx-closure-and-object-identities)
  ebTxsServeLoop : Node → Link × Dir → Proc
  ebTxsServeLoop n (l , d) = loop0 (ebTxsServeBody n l (opposite d))

  -- deposit every transaction pulled off the wire
  putAllTx : Node → List Tx → Proc
  putAllTx n []         = Skip
  putAllTx n (tx ∷ txs) = putTxEv n ! tx ⟶ putAllTx n txs

  -- one TxSubmission PULL round: ask for ids, then for those txs, then deposit them.
  -- This drives the protocol's REQUESTER (`TxSubmission.serverStep` = `TSserverA`),
  -- which is a SERVER peer, hence direction `opposite d`.
  tsPullBody : Node → Link → Dir → Proc
  tsPullBody n l d =
    apiTS l d sendTSRequestTxIdsBlocking ! (0 , 1) ⟶
      (apiTS l d recvTSReplyTxIds ⟶ (λ ids →
        Output ⦃ DecEqI.DecEq-List ⦄ (apiTS l d sendTSRequestTxsPipelined) ids
          (apiTS l d recvTSReplyTxs ⟶ putAllTx n)))

  -- the TxSubmission pull thread of one endpoint.  IT DRIVES `opposite d`.
  tsPull : Node → Link × Dir → Proc
  tsPull n (l , d) = loop0 (tsPullBody n l (opposite d))

  -- one TxSubmission SERVE round with a read pointer: answer an id request with the
  -- k-th oldest mempool transaction's HASH and the following tx request with that
  -- transaction, then advance.  `txData` is gone: a transaction is OPAQUE and can only be
  -- SERVED out of the mempool, never rebuilt from its hash, so this round now really does
  -- move an id and then a body.  This drives the protocol's SUBMITTER
  -- (`TxSubmission.clientStep` = `TSclientA`), which is a CLIENT peer, hence `d`.
  tsServeBody : Node → Link → Dir → ℕ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ
  tsServeBody n l d k =
    apiTS l d recvTSRequestTxIds ⟶ (λ _ →
      getTxAtEv n k ⟶ (λ tx →
        Output ⦃ DecEqI.DecEq-List ⦄ (apiTS l d sendTSReplyTxIds) (txHash tx ∷ [])
          (apiTS l d recvTSRequestTxs ⟶ (λ _ →
            Output ⦃ DecEqI.DecEq-List ⦄ (apiTS l d sendTSReplyTxs) (tx ∷ [])
              (Ret (suc k))))))

  -- the TxSubmission serve thread of one endpoint.  IT DRIVES `d`.
  tsServe : Node → Link × Dir → Proc
  tsServe n (l , d) = loop (tsServeBody n l d) 0

  ------------------------------------------------------------------------
  -- Assembly
  ------------------------------------------------------------------------

  -- the TEN threads of one endpoint: the Praos relay pair, the LN announcer, the ONE
  -- Notify client, the body and vote offerers, the two LF servers (bodies and tx
  -- closures) and the TxSubmission pull/serve pair.  `voteServeLoop` is gone;
  -- `ebTxsServeLoop` takes its place, so the count is still ten.
  endpointThreadsL : Node → Link × Dir → Proc
  endpointThreadsL n e =
    clientLoop n e
      ⦀ (serverLoopL n e
      ⦀ (lnClientLoopL n e
      ⦀ (lnServerLoopL n e
      ⦀ (bodyOfferLoop n e
      ⦀ (voteOfferLoop n e
      ⦀ (ebServeLoop n e
      ⦀ (ebTxsServeLoop n e
      ⦀ (tsPull n e ⦀ tsServe n e))))))))

  -- every incident endpoint's ten threads, interleaved in `endpointsOf`'s order
  -- (`⦀` is not commutative up to `≡`, so that order is part of the interface)
  allThreadsL : Node → Proc
  allThreadsL n =
    ⦀⁺ (endpointThreadsL n (proj₁ (endpointsOf n)))
       (map (endpointThreadsL n) (proj₂ (endpointsOf n)))

  -- THE LINEAR-LEIOS NODE LOGIC: the SIX node-level threads and every endpoint's ten, all
  -- interleaved, synchronised with the node's five stores on `storeES`
  nodeLogicL : Node → StateL → Proc
  nodeLogicL n (held , es , bs , ts , vs) =
    (forgeL n ⦀ (forgeCert n ⦀ (ebIndex n ⦀ (voter n ⦀ (submit n ⦀
       (certSink n ⦀ allThreadsL n))))))
      ∥⇘ storeES ⇙
    (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀ (mempool n ts ⦀ voteStore n vs))))

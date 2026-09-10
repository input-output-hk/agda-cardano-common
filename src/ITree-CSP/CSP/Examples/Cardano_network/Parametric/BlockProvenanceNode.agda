{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — BLOCK PROVENANCE AT THE NODE'S LEAVES: the
-- store and the four relay threads are well-formed (`BlockProvenance.Wf`).
--
-- `Parametric.BlockProvenance` supplies the assume-guarantee carrier `Wf`
-- and its congruences but proves no leaf fact.  This module proves the
-- node-local ones, and the whole argument turns on ONE fact about the
-- source of every block in the network:
--
--   THE SEED.  `NodeLogic.acceptMint` admits a mint `(me , b)` iff
--   `announcedEB b ≡ map ebHash me`, and that guard IS
--   `WellAnnounced (mintedAfter (me , b) ms) b`: `me = nothing` gives the
--   left injection outright, `me = just e` gives `ebHash e`, which
--   `mintedAfter` has just prepended (`mint-seed` below).  So the store's
--   mint clause — the only place a block enters the network from
--   outside — re-establishes the invariant one step after the unpinned
--   `env … envMint` event, which is why that event is exempt from
--   `Carries`.  The `stPut` clause is unguarded and RELIES on the
--   deposited block instead: that is the assume-guarantee split, and
--   `Wf`'s `stepW` hands the rely over (`storeBody`).
--
-- EVERY THREAD IS A RELAY.  `clientLoop` carries a block from
-- `apiBF recvBFBlock` (rely) to `store stPut` (guarantee) across three
-- prefixes, `serverLoop` from `store stGet` (rely) to `apiBF sendBFBlock`
-- (guarantee) across six, `lnServerLoop` from `store stGet` (rely) to the
-- announcement (guarantee) across two; `mint` and `lnClientLoop` touch no
-- block-carrying channel and are vacuous.  In every case the block lives
-- in a lambda-bound register that outlives no prefix, so the guarantee is
-- `wellAnnounced-mono` of the rely along the states the prefixes visit.
--
-- THE GUARANTEE ALPHABETS.  `wf-Par`'s side condition `Sep` demands that
-- outside the synchronisation set both operands' alphabets agree on the
-- block-carrying labels, and `wf-⦀` demands ONE alphabet for all
-- interleaved threads.  So the alphabets are cut from a single node-level
-- one: `nodeG` is every label except the node's ONE external rely, a block
-- received off the BlockFetch api; the store's `storeG` is `nodeG` minus
-- its own rely `stPut`, the threads' `threadsG` is `nodeG` minus theirs,
-- `stGet`.  Both store relies are `storeES`-synchronised, so
-- `storeG ∪ threadsG = nodeG` and `Sep storeES` is by reduction on the
-- seven `Carries` shapes.  (Task 5 spends this; nothing here does.)
--
-- THE MACHINERY lives next door, in `Parametric.BlockProvenanceWfR`:
-- `Wf` is stated for unit-returning trees, but the store body returns its
-- new `Held` and the loops are `iter`s over `_>>=_`-shaped bodies, so
-- `BlockProvenanceWfR.Body` adds the returning-tree carrier `WfR` and the
-- closure lemmas for exactly the operators `NodeLogic` uses.  That half is
-- generic and is deliberately a separate compilation unit: elaborated
-- together with the instantiation below it does not typecheck in
-- reasonable time (an hour and a half, unfinished; apart, 24s + 6m).
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.BlockProvenanceNode where

open import Level using (Level; 0ℓ; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.Any using (here)
import Data.List.Relation.Unary.All as All
open All using (All)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees
  using ( PTree; ptree; NodeKind; ret; sil; react; AnyTypes; ExtI; ContinueType
        ; deadlock; sil-injective; react-injective )
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; opposite)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import Semantics.LTS as LTS
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceWfR as BPW

------------------------------------------------------------------------
-- The Cardano instance: the store and the threads
------------------------------------------------------------------------

-- parametric in the network parameters, the topology and the api alphabet — the same
-- three parameters every other `Parametric.Announce*`/`BlockProvenance` module takes
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  -- the SAME opens as `NodeLogic`, so the `_≟_` and `_□_` instances elaborate to the
  -- terms `acceptMint`/`storeStep` were built with
  open Params p using (Block; EB; EBHash; time₀; length₀; decBlock; ebHash; announcedEB)
  open N p
    using ( Link; Net_Api; Net_Api-≟; env; envMint; apiLN; store; apiCS; apiBF
          ; stGet; stPut
          ; sendBFRequestRange; reqBFRange; sendBFStartBatch; sendBFBlock
          ; sendBFBatchDone; recvBFBlock
          ; sendLNRequestNext; recvLNBlockAnnouncement; sendLNBlockAnnouncement
          ; recvCSRollforward )
  open D p
    using ( Payload; Point; Header; Tip; ChainRange; header; tip; chainRange
          ; DecEq-Point; DecEq-Header; DecEq-Tip; DecEq-ChainRange; DecEq-Payload )
  open import CSP.Examples.Cardano_network.Base using (Dir)
  open Topology t using (Node; endpointsOf)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (_⦀_; ⦀⁺; Prefix; Output; Ret; _□_)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES using (Proc)
  open NL.Generic p t apiES
    using ( Held; StoreProc; homeOf; mintEv; putEv; getEv; offerHeld; acceptMint
          ; storeStep; blockStore; mint; clientBody-k; clientLoop; serverBody-k
          ; serverLoop; lnServerLoop; lnClientLoop; endpointThreads; allThreads )
  open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; evLabel)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload}) using (Alpha)
  open AS.Generic p t apiES using (Minted)
  open AI.Generic p t apiES using (WellAnnounced; wellAnnounced-mono; mintedAfter)
  open BP.Generic p t apiES
  open BPW.Body (Net_Api-≟ {Payload}) Minted Block Carries WellAnnounced
            next _⊆_ ⊆-refl ⊆-trans next-⊇

  -- product `DecEq` for the `sendCSRollForward` carrier (`Header × Tip`) — the same
  -- instance `NodeLogic` declares, so `wfR-Output` sees the one the `!`-output in
  -- `serverBody-k` was built with (as `AnnounceSafeLeaves` does for `OffersOnly-Output`)
  instance
    DecEq-Header×Tip : DecEq (Header × Tip)
    DecEq-Header×Tip = DecEqI.DecEq-×

  ------------------------------------------------------------------------
  -- The guarantee alphabets
  ------------------------------------------------------------------------

  -- THE NODE'S ALPHABET: every label but its one external rely, a block received off
  -- the BlockFetch api.  Both leaf alphabets are cut from this one (see the header).
  nodeG : Alpha
  nodeG (_ , apiBF _ _ recvBFBlock) _ = ⊥
  nodeG _                           _ = ⊤

  -- the store's: `nodeG` minus its own rely, a deposit
  storeG : Alpha
  storeG (_ , store _ _ stPut) _ = ⊥
  storeG at                    a = nodeG at a

  -- the threads': `nodeG` minus theirs, a block taken from the store
  threadsG : Alpha
  threadsG (_ , store _ _ stGet) _ = ⊥
  threadsG at                    a = nodeG at a

  ------------------------------------------------------------------------
  -- `BlockOK` at the channel shapes the leaves use
  ------------------------------------------------------------------------

  -- the vacuous ones: no `Carries` constructor names these channels
  blockOK-bfRange : ∀ {ms l d x} → BlockOK ms (ev (evl (evLabel _ (apiBF l d sendBFRequestRange) x)))
  blockOK-bfRange ()
  blockOK-bfReq   : ∀ {ms l d x} → BlockOK ms (ev (evl (evLabel _ (apiBF l d reqBFRange) x)))
  blockOK-bfReq ()
  blockOK-bfStart : ∀ {ms l d x} → BlockOK ms (ev (evl (evLabel _ (apiBF l d sendBFStartBatch) x)))
  blockOK-bfStart ()
  blockOK-bfDone  : ∀ {ms l d x} → BlockOK ms (ev (evl (evLabel _ (apiBF l d sendBFBatchDone) x)))
  blockOK-bfDone ()
  blockOK-lnReq   : ∀ {ms l d x} → BlockOK ms (ev (evl (evLabel _ (apiLN l d sendLNRequestNext) x)))
  blockOK-lnReq ()
  blockOK-lnRecv  : ∀ {ms l d x} → BlockOK ms (ev (evl (evLabel _ (apiLN l d recvLNBlockAnnouncement) x)))
  blockOK-lnRecv ()

  -- the guarantees: a well-announced block on each block-carrying channel a leaf emits
  ok-stGet  : ∀ {ms l d b} → WellAnnounced ms b → BlockOK ms (ev (evl (evLabel _ (store l d stGet) b)))
  ok-stGet wa c-stGet = wa
  ok-stPut  : ∀ {ms l d b} → WellAnnounced ms b → BlockOK ms (ev (evl (evLabel _ (store l d stPut) b)))
  ok-stPut wa c-stPut = wa
  ok-sendBF : ∀ {ms l d b} → WellAnnounced ms b → BlockOK ms (ev (evl (evLabel _ (apiBF l d sendBFBlock) b)))
  ok-sendBF wa c-sendBF = wa
  ok-ann    : ∀ {ms l d b} → WellAnnounced ms b
            → BlockOK ms (ev (evl (evLabel _ (apiLN l d sendLNBlockAnnouncement) (header b))))
  ok-ann wa c-ann = wa

  ------------------------------------------------------------------------
  -- The store
  ------------------------------------------------------------------------

  -- THE STORE'S INVARIANT: every held block is well-announced
  StoreInv : Minted → Held → Set
  StoreInv ms held = All (WellAnnounced ms) held

  -- monotone in the minted set, blockwise
  storeInv-mono : ∀ {ms ms′ held} → ms ⊆ ms′ → StoreInv ms held → StoreInv ms′ held
  storeInv-mono sub = All.map (wellAnnounced-mono sub)

  -- THE SEED.  `acceptMint`'s guard, `announcedEB b ≡ map ebHash me`, is exactly
  -- well-announcedness of `b` against the minted set the mint grows to.
  mint-seed : ∀ {ms} me b → announcedEB b ≡ Data.Maybe.map ebHash me
            → WellAnnounced (mintedAfter (me , b) ms) b
  mint-seed nothing  b eq = inj₁ eq
  mint-seed (just e) b eq = inj₂ (ebHash e , eq , here refl)

  -- …so the store `acceptMint` leaves is well-announced at every superset of the grown
  -- set: the accepted block by the seed, the rest by monotonicity, a rejected mint by
  -- monotonicity alone.  The `with` mirrors `acceptMint`'s own.
  acceptMint-wa : ∀ n {ms held} me b → StoreInv ms held
                → ∀ {ms′} → next (lbl (mintEv n) (me , b)) ms ⊆ ms′
                → StoreInv ms′ (acceptMint (me , b) held)
  acceptMint-wa n {ms} me b inv le with announcedEB b ≟ Data.Maybe.map ebHash me
  ... | yes eq = wellAnnounced-mono (subst (λ xs → xs ⊆ _) (next-mint (me , b) ms) le)
                                    (mint-seed me b eq)
                 All.∷ storeInv-mono (⊆-trans (next-⊇ _ ms) le) inv
  ... | no  _  = storeInv-mono (⊆-trans (next-⊇ _ ms) le) inv

  -- every `□` of the store is of stable operands
  stable-offerHeld : ∀ n held bs → Stable (offerHeld n held bs)
  stable-offerHeld n held []       = stable-node refl
  stable-offerHeld n held (b ∷ bs) = stable-□ (stable-node refl) (stable-offerHeld n held bs)

  -- THE GUARANTEE: every block the store offers on `stGet` is a held one, hence
  -- well-announced; the state is left as it was
  offerHeld-wf : ∀ n {ms held} → StoreInv ms held → ∀ bs → All (WellAnnounced ms) bs
               → WfR storeG ms StoreInv (offerHeld n held bs)
  offerHeld-wf n inv []       _              = wfR-Stop
  offerHeld-wf n {held = held} inv (b ∷ bs) (wb All.∷ wbs) =
    wfR-□ (getEv n ! b ⟶ Ret held) (offerHeld n held bs)
      (stable-node refl) (stable-offerHeld n held bs)
      (wfR-Output (λ le _ → ok-stGet (wellAnnounced-mono le wb))
                  (λ le _ → wfR-Ret (λ le′ → storeInv-mono (⊆-trans le le′) inv)))
      (offerHeld-wf n inv bs wbs)

  -- ONE STORE STEP.  Three clauses: the mint — value unpinned, `BlockOK` vacuous
  -- (`blockOK-mint`), the invariant restored by the seed; the deposit — THE RELY,
  -- `BlockOK ms (put ! b)` is `WellAnnounced ms b`, handed over by `stepR`, so the
  -- unguarded `b ∷ held` is fine; and the offers — the guarantee above.
  storeBody : ∀ n {ms held} → StoreInv ms held → WfR storeG ms StoreInv (storeStep n held)
  storeBody n {held = held} inv =
    wfR-□ (mintEv n ⟶ (λ mb → Ret (acceptMint mb held)))
          ((putEv n ⟶ (λ b → Ret (b ∷ held))) □ offerHeld n held held)
      (stable-node refl) (stable-□ (stable-node refl) (stable-offerHeld n held held))
      (wfR-Prefix (λ _ _ _ → blockOK-mint)
                  (λ le mb _ → wfR-Ret (acceptMint-wa n (proj₁ mb) (proj₂ mb) (storeInv-mono le inv))))
      (wfR-□ (putEv n ⟶ (λ b → Ret (b ∷ held))) (offerHeld n held held)
        (stable-node refl) (stable-offerHeld n held held)
        (wfR-Prefix (λ _ _ g → ⊥-elim g)
                    (λ le b ok → wfR-Ret (λ le′ →
                       wellAnnounced-mono le′ (ok c-stPut) All.∷ storeInv-mono (⊆-trans le le′) inv)))
        (offerHeld-wf n inv held inv))

  -- THE STORE: well-formed on `storeG` whenever what it holds is well-announced
  wf-blockStore : ∀ {ms held} n → StoreInv ms held → Wf storeG ms (blockStore n held)
  wf-blockStore n inv = wf-loop (λ le _ → storeInv-mono le) (λ _ _ → storeBody n) inv

  ------------------------------------------------------------------------
  -- The threads
  ------------------------------------------------------------------------

  -- the mint thread: `env … envMint` carries no constrained block
  wf-mint : ∀ {ms} n → Wf threadsG ms (mint n)
  wf-mint n = wf-loop0 (wfR-Prefix (λ _ _ _ → blockOK-mint) (λ _ _ _ → wfR-Ret (λ _ → tt)))

  -- the LN client thread: neither api event carries a block
  wf-lnClientLoop : ∀ {ms} (ld : Link × Dir) → Wf threadsG ms (lnClientLoop ld)
  wf-lnClientLoop (l , d) =
    wf-loop0 (wfR-Prefix (λ _ _ _ → blockOK-lnReq)
      (λ _ _ _ → wfR-Prefix (λ _ _ _ → blockOK-lnRecv) (λ _ _ _ → wfR-Ret (λ _ → tt))))

  -- THE CLIENT THREAD: relies at `apiBF recvBFBlock` (excluded from `threadsG`), and
  -- deposits that very block at `stPut` one prefix later
  wf-clientLoop : ∀ {ms} n (ld : Link × Dir) → Wf threadsG ms (clientLoop n ld)
  wf-clientLoop n (l , d) =
    wf-loop0 (wfR-Prefix (λ _ _ _ → blockOK-apiCS) (λ _ _ _ → wfR-Prefix (λ _ _ _ → blockOK-apiCS) k))
    where
    -- the RollForward continuation: request the range, receive the block, store it
    -- (the tag is PINNED: `Header × Tip` is the carrier of `sendCSRollForward` too,
    -- so an underscore here leaves the tag meta unsolvable)
    k : ∀ {s s′} → s ⊆ s′ → ∀ a → BlockOK s′ (lbl (apiCS l d recvCSRollforward) a)
      → WfR threadsG (next (lbl (apiCS l d recvCSRollforward) a) s′) (λ _ _ → ⊤)
            (clientBody-k n l d a)
    k _ (header b , _) _ =
      wfR-Output (λ _ _ → blockOK-bfRange) (λ _ _ →
        wfR-Prefix (λ _ _ g → ⊥-elim g) (λ le b′ ok →
          wfR-Output (λ le′ _ → ok-stPut (wellAnnounced-mono le′ (ok c-recvBF)))
                     (λ _ _ → wfR-Ret (λ _ → tt))))

  -- THE SERVER THREAD: relies at `stGet` (excluded from `threadsG`), and serves that
  -- block at `apiBF sendBFBlock` five prefixes later
  wf-serverLoop : ∀ {ms} n (ld : Link × Dir) → Wf threadsG ms (serverLoop n ld)
  wf-serverLoop n (l , d) =
    wf-loop0 (wfR-Prefix (λ _ _ _ → blockOK-apiCS)
      (λ _ _ _ → wfR-Prefix (λ _ _ g → ⊥-elim g) (λ _ b ok → k b (ok c-stGet))))
    where
    -- the tail of a server round on a well-announced block
    k : ∀ {s} b → WellAnnounced s b → WfR threadsG s (λ _ _ → ⊤) (serverBody-k n l (opposite d) b)
    k b wa =
      wfR-Prefix (λ _ _ _ → blockOK-apiCS) (λ le₁ _ _ →
      wfR-Output (λ _ _ → blockOK-apiCS) (λ le₂ _ →
      wfR-Prefix (λ _ _ _ → blockOK-bfReq) (λ le₃ _ _ →
      wfR-Prefix (λ _ _ _ → blockOK-bfStart) (λ le₄ _ _ →
      wfR-Output (λ le₅ _ → ok-sendBF (wellAnnounced-mono
                     (⊆-trans le₁ (⊆-trans le₂ (⊆-trans le₃ (⊆-trans le₄ le₅)))) wa)) (λ _ _ →
      wfR-Prefix (λ _ _ _ → blockOK-bfDone) (λ _ _ _ → wfR-Ret (λ _ → tt)))))))

  -- THE ANNOUNCER: relies at `stGet`, announces that block one prefix later — this is
  -- the leaf `wf→gate` turns into `Safe`'s `gate`
  wf-lnServerLoop : ∀ {ms} n (ld : Link × Dir) → Wf threadsG ms (lnServerLoop n ld)
  wf-lnServerLoop n (l , d) =
    wf-loop0 (wfR-Prefix (λ _ _ g → ⊥-elim g) (λ _ b ok →
      wfR-Output (λ le′ _ → ok-ann (wellAnnounced-mono le′ (ok c-stGet)))
                 (λ _ _ → wfR-Ret (λ _ → tt))))

  -- one endpoint's quadruple, and every endpoint's, all on `threadsG`
  wf-endpointThreads : ∀ {ms} n (e : Link × Dir) → Wf threadsG ms (endpointThreads n e)
  wf-endpointThreads n e =
    wf-⦀ (wf-clientLoop n e)
         (wf-⦀ (wf-serverLoop n e) (wf-⦀ (wf-lnClientLoop e) (wf-lnServerLoop n e)))

  wf-allThreads : ∀ {ms} n → Wf threadsG ms (allThreads n)
  wf-allThreads n =
    wf-⦀⁺ (endpointThreads n) (proj₁ (endpointsOf n)) (proj₂ (endpointsOf n)) (wf-endpointThreads n)

  -- the mint thread and every endpoint's threads: the store's whole partner in
  -- `nodeLogic`, on `threadsG`
  wf-threads : ∀ {ms} n → Wf threadsG ms (mint n ⦀ allThreads n)
  wf-threads n = wf-⦀ (wf-mint n) (wf-allThreads n)

  ------------------------------------------------------------------------
  -- Non-vacuity: the announce channel is in the threads' alphabet
  ------------------------------------------------------------------------

  -- so `wf→gate` applies to every thread fact above (and to their interleavings)
  annIn-threadsG : AnnIn threadsG
  annIn-threadsG _ = tt

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — ANNOUNCEMENT SAFETY AT `nodeLogicL`'s FIFTEEN
-- THREAD FAMILIES, and the node-level join: the thread half of the S0 leaf
-- layer, in the ANNOUNCE discipline (`Parametric.BlockProvenance`'s
-- `Carries`/`WellAnnounced`/`next`).
--
-- The counterpart of `Leios/AnnounceStoreL.agda` (the store half) and of
-- `BlockProvenanceNode.agda:258-336` (the thread half of the RELAY node
-- logic).  Nothing in `NodeLogicL.agda` is touched.
--
-- THE ALPHABET IS *NOT* QUITE FREE — one correction to the plan.  The store
-- half found, correctly, that `nodeLogicL` adds no block-carrying channel
-- beyond `NodeLogic`'s, so `BlockProvenanceNode`'s `nodeG` and `storeG`
-- transfer verbatim.  `threadsG` does NOT: it excludes only `store … stGet`,
-- the relay threads' one rely, whereas FIVE of `nodeLogicL`'s threads read a
-- block through the READ-POINTER channel `store … (stGetAt k)` instead
-- (`ebIndexBody`, `voterBody`, `serverBodyL`, `lnServerBodyL`,
-- `bodyOfferBody`).  `Carries` names that channel (`c-stGetAt`, added for the
-- store half), and a thread cannot GUARANTEE a block it was handed, so
-- `stGetAt` has to leave the threads' alphabet exactly as `stGet` did.
-- `threadsGL` below is therefore `threadsG` minus it — written as a PRODUCT
-- with `NotGetAt` so that `threadsGL ⊆ threadsG` is `proj₁` and
-- `BlockProvenanceNode.wf-clientLoop` transfers for free.  `storeG`, `nodeG`,
-- `StoreInv` and every leaf lemma are imported unchanged, and the node-level
-- statement `wf-nodeLogicL : Wf nodeG …` is the one the plan asked for.
--
-- `sep-storeL` is the one-line variant of `AnnounceSafeCopy.sep-store`: both
-- relies, `stPut` on the store side and `stGet`/`stGetAt` on the threads',
-- are `store` labels and hence `storeES`-synchronised, so every clause either
-- refutes the alphabet membership or refutes the non-membership.
--
-- WHAT EACH THREAD COSTS.  Eleven are VACUOUS — they touch no channel
-- `Carries` names, so every obligation is an absurd pattern — but four of
-- those carry sub-recursions (`putChecked`, `putAllVotes`, `putAllTx`,
-- `serveTxs`) with no analogue in the store half.  Three are CONTENT-BEARING:
--
--   * `forgeL` — the only thread that DEPOSITS.  A certificate-carrying RB is
--     withheld by `acceptForgeL` and reaches `held` through this thread's own
--     `putEv`, so the `c-stPut` guarantee is owed here.  It is paid by THE
--     SEED: `forgeOK` is `⌊_⌋` of the very decision `NodeLogic.acceptForge`
--     makes, so under a `true` guard the block is well-announced against the
--     set the forge event itself grew (`forge-seed`, `next-forge`).
--   * `serverLoopL` — reads at `stGetAt` and serves at `apiBF … sendBFBlock`
--     five prefixes later.  This is why `c-stGetAt` exists at all.
--   * `lnServerLoopL` — THE ANNOUNCE LEAF, and the whole point of S0: it
--     reads at `stGetAt` and announces `header b` on
--     `apiLP … lnpSendBlockAnnouncement`, which `Carries` names (`c-annP`).
--     `annIn-threadsGL` then makes `wf→gate` apply, on BOTH announce channels.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.AnnounceThreadsL where

open import Level using (Level; 0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI
open import Class.DecEq.Instances using (DecEq-List)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Topology using (Topology; opposite)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Net as N
import Cardano_network.Data as D
import CSP.Operators as O
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.AnnounceSafe as AS
import Cardano_network.Parametric.AnnounceInvariant as AI
import Cardano_network.Parametric.BlockProvenance as BP
import Cardano_network.Parametric.BlockProvenanceWfR as BPW
import Cardano_network.Parametric.BlockProvenanceNode as BPN
import Cardano_network.Parametric.Leios.AnnounceStoreL as ASL

-- the announce discipline at `nodeLogicL`'s threads, parametric in the same five
-- arguments `NodeLogicL.Generic` takes, so the threads below are literally its terms
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open Params p
    using ( Block; LSlot; VoteBlob; EB; EBHash; RbHash; Tx; TxHash; Size
          ; ebHash; rbHash; txHash; slotOf; announcedEB
          ; decBlock; decEBHash; decLSlot; decVoteBlob; decEB
          ; decRbHash; decTx; decTxHash )
  open LeiosP p using (LeiosEb; LeiosPoint; DecEq-LeiosPoint)
  open LeiosP.LeiosParams lp using (rbCert; ebTxs)
  open N p
    using ( Link; Net_Api; Net_Api-≟; store; env; break
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; apiLP
          ; stPut; stGet; stGetAt; stPutEB; stGetEBAt; stPutBody; stGetBody
          ; stPutTx; stGetTxAt; stGetTx; stPutVote; stGetVoteAt; stCert; stHasCert
          ; envForge; envSubmit; lnpSendBlockAnnouncement )
  -- `Data.DecEq-Tx` is deliberately NOT opened, so `decTx` is the ONE `DecEq Tx` in
  -- scope and instance search resolves the very term `NodeLogicL` used
  open D p
    using ( Payload; Point; Header; Tip; ChainRange; header; tip; chainRange
          ; TxBitmap
          ; DecEq-Point; DecEq-Header; DecEq-Tip; DecEq-ChainRange; DecEq-Payload
          ; DecEq-EBPoint; DecEq-TxBitmap; DecEq-TxEntries
          ; DecEq-TxsRequest; DecEq-TxsReply; DecEq-Offer )
  open import Cardano_network.Base using (Dir)
  open Topology t using (Node; endpointsOf)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (EventSet; _⦀_; ⦀⁺; _□_; _◁_▷_; _>>_; Ret; Stop; Skip; Prefix; Output)
  open import Cardano_network.Parametric.Node p t apiES using (Proc)
  open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; √; evLabel)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload}) using (Alpha)
  open NL.Generic p t apiES
    using ( Held; homeOf; forgeEv; putEv; storeES; clientLoop; serverBody-k )
  open NLL.Generic p lp t apiES voterOf
    using ( DecEq-⊤poly; DecEq-ℕ×ℕ
          ; memberOf
          ; Entries; Bodies; Mem; Votes; StateL
          ; at?; getAtEv; putEBEv; putBodyEv; getBodyEv
          ; putTxEv; getTxAtEv; getTxEv; putVoteEv; getVoteAtEv
          ; certEv; hasCertEv; submitEv
          ; forgeOK; forgeCertL; forgeBodyL; forgeL
          ; ebIndexBody; ebIndex; voterBody; voter; submit; certSink
          ; serverBodyL; serverLoopL; lnServerBodyL; lnServerLoopL
          ; bodyOfferBody; bodyOfferLoop; voteOfferBody; voteOfferLoop; awaitTxs
          ; fetchBody; putChecked; fetchTxs; putAllVotes
          ; lnClientBodyL; lnClientLoopL
          ; ebServeBody; ebServeLoop; serveTxs; ebTxsServeBody; ebTxsServeLoop
          ; putAllTx; tsPullBody; tsPull; tsServeBody; tsServe
          ; endpointThreadsL; allThreadsL; nodeLogicL )
  open AS.Generic p t apiES using (Forged)
  open AI.Generic p t apiES using (WellAnnounced; wellAnnounced-mono)
  -- the announce carrier, wholesale (`Carries`, `next`, `next-⊇`, `BlockOK`, `Wf`, …)
  open BP.Generic p t apiES
  -- … and its returning-tree layer at exactly the arguments `BlockProvenanceNode`
  -- opened it with, so the two `Wf`/`WfR` records are the same records
  open BPW.Body (Net_Api-≟ {Payload}) Forged Block Carries WellAnnounced
            next _⊆_ ⊆-refl ⊆-trans next-⊇
  -- the node/store alphabets, the store invariant and every RELAY leaf fact, verbatim
  open BPN.Generic p t apiES
    using ( nodeG; storeG; threadsG; StoreInv; forge-seed
          ; blockOK-bfRange; blockOK-bfReq; blockOK-bfStart; blockOK-bfDone
          ; ok-stPut; ok-sendBF; wf-clientLoop )
  -- the store half of S0
  open ASL.Generic p lp t apiES voterOf using (wf-storesL)

  instance
    -- product `DecEq` for the `sendCSRollForward` carrier (`Header × Tip`) — the same
    -- instance `NodeLogic` and `BlockProvenanceNode` declare, so `wfR-Output` sees the
    -- one the `!`-output in `serverBody-k` was built with
    DecEq-Header×Tip : DecEq (Header × Tip)
    DecEq-Header×Tip = DecEqI.DecEq-×

  ------------------------------------------------------------------------
  -- The threads' guarantee alphabet
  ------------------------------------------------------------------------

  -- NOT the read-pointer channel: `store … (stGetAt k)` is the threads' SECOND rely,
  -- beside `stGet`, because five of them read a held block through it
  NotGetAt : AnyTypes (Net_Api Payload) → Set
  NotGetAt (_ , store _ _ (stGetAt _)) = ⊥
  NotGetAt _                           = ⊤

  -- THE THREADS' ALPHABET: `BlockProvenanceNode.threadsG` minus the read-pointer rely.
  -- A PRODUCT rather than a fresh case split, so that `threadsGL ⊆ threadsG` is `proj₁`
  -- and every relay leaf of `BlockProvenanceNode` transfers by `wf-mono-G`.
  threadsGL : Alpha
  threadsGL at a = threadsG at a × NotGetAt at

  -- store vs threads at `storeES`, the `nodeLogicL` variant of
  -- `AnnounceSafeCopy.sep-store`: all three relies are `store` labels, hence
  -- synchronised; every other block-carrying label is in both alphabets
  sep-storeL : Sep storeES threadsGL storeG
  sep-storeL =
      (λ { c-stGet   (() , _) _  ; c-stGetAt (_ , ()) _
         ; c-stPut   _  ¬m → ⊥-elim (¬m tt)
         ; c-sendBF  _  _  → tt  ; c-recvBF  (() , _) _
         ; c-ann     _  _  → tt  ; c-annP    _ _ → tt
         ; c-input   _  _  → tt  ; c-output  _ _ → tt })
    , (λ { c-stGet   _ ¬m → ⊥-elim (¬m tt) ; c-stPut () _
         ; c-stGetAt _ ¬m → ⊥-elim (¬m tt)
         ; c-sendBF  _ _ → tt , tt ; c-recvBF () _
         ; c-ann     _ _ → tt , tt ; c-annP   _ _ → tt , tt
         ; c-input   _ _ → tt , tt ; c-output _ _ → tt , tt })

  -- `nodeG` IS COVERED by the two leaf alphabets: a deposit is guaranteed by the
  -- threads, every other label by the store.  One clause per `Net_Api` constructor and
  -- one per `StoreTag`, because neither alphabet reduces until the constructor is known
  -- (a catch-all would leave `storeG at a` stuck on a variable `at`).
  nodeG⊆ : ∀ at a → nodeG at a → (threadsGL ∪α storeG) at a
  nodeG⊆ (_ , store _ _ stPut)           a g = inj₁ (g , tt)
  nodeG⊆ (_ , store _ _ stGet)           a g = inj₂ g
  nodeG⊆ (_ , store _ _ (stGetAt _))     a g = inj₂ g
  nodeG⊆ (_ , store _ _ stPutEB)         a g = inj₂ g
  nodeG⊆ (_ , store _ _ (stGetEBAt _))   a g = inj₂ g
  nodeG⊆ (_ , store _ _ stPutBody)       a g = inj₂ g
  nodeG⊆ (_ , store _ _ (stGetBody _))   a g = inj₂ g
  nodeG⊆ (_ , store _ _ stPutTx)         a g = inj₂ g
  nodeG⊆ (_ , store _ _ (stGetTxAt _))   a g = inj₂ g
  nodeG⊆ (_ , store _ _ (stGetTx _))     a g = inj₂ g
  nodeG⊆ (_ , store _ _ stPutVote)       a g = inj₂ g
  nodeG⊆ (_ , store _ _ (stGetVoteAt _)) a g = inj₂ g
  nodeG⊆ (_ , store _ _ stCert)          a g = inj₂ g
  nodeG⊆ (_ , store _ _ (stHasCert _))   a g = inj₂ g
  nodeG⊆ (_ , env    _ _ _) a g = inj₂ g
  nodeG⊆ (_ , input  _ _ _) a g = inj₂ g
  nodeG⊆ (_ , output _ _ _) a g = inj₂ g
  nodeG⊆ (_ , sndmsg _ _ _) a g = inj₂ g
  nodeG⊆ (_ , rcvmsg _ _ _) a g = inj₂ g
  nodeG⊆ (_ , tx     _ _ _) a g = inj₂ g
  nodeG⊆ (_ , sndack _ _ _) a g = inj₂ g
  nodeG⊆ (_ , rcvack _ _ _) a g = inj₂ g
  nodeG⊆ (_ , ack    _ _ _) a g = inj₂ g
  nodeG⊆ (_ , done   _ _ _) a g = inj₂ g
  nodeG⊆ (_ , apiCS  _ _ _) a g = inj₂ g
  nodeG⊆ (_ , apiBF  _ _ _) a g = inj₂ g
  nodeG⊆ (_ , apiTS  _ _ _) a g = inj₂ g
  nodeG⊆ (_ , apiKA  _ _ _) a g = inj₂ g
  nodeG⊆ (_ , apiLN  _ _ _) a g = inj₂ g
  nodeG⊆ (_ , apiLF  _ _ _) a g = inj₂ g
  nodeG⊆ (_ , apiLP  _ _ _) a g = inj₂ g
  nodeG⊆ (_ , break  _)     a g = inj₂ g

  ------------------------------------------------------------------------
  -- Two shape combinators the thread half needs and the store half did not
  ------------------------------------------------------------------------

  -- a conditional is well-formed when the arm its guard selects is; the arm receives
  -- the guard's VALUE as an equation, which is what `forgeL` spends
  wfR-if : ∀ {ℓr} {R : Set ℓr} {G : Alpha} {ms} {Inv : Forged → R → Set}
             {P Q : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R} (c : Bool)
         → (c ≡ true  → WfR G ms Inv P)
         → (c ≡ false → WfR G ms Inv Q)
         → WfR G ms Inv (P ◁ c ▷ Q)
  wfR-if true  h hz = h  refl
  wfR-if false h hz = hz refl

  -- a `maybe′` (equivalently a `maybe` at a constant motive) is well-formed when both
  -- arms are — the shape of `forgeCertL`, `ebIndexBody`, `voterBody` and `bodyOfferBody`
  wfR-maybe : ∀ {ℓr} {R : Set ℓr} {A : Set} {G : Alpha} {ms} {Inv : Forged → R → Set}
                {f : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
                {z : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R} (mx : Maybe A)
            → (∀ x → WfR G ms Inv (f x)) → WfR G ms Inv z
            → WfR G ms Inv (Data.Maybe.maybe′ f z mx)
  wfR-maybe (just x) h hz = h x
  wfR-maybe nothing  h hz = hz

  ------------------------------------------------------------------------
  -- The one announce guarantee `BlockProvenanceNode` does not already have
  ------------------------------------------------------------------------

  -- the PROTOTYPE announce channel, the one `lnServerLoopL` fires: `BlockOK` at an
  -- announcement of `header b` is well-announcedness of `b` (`c-annP`)
  ok-annP : ∀ {ms l d b} → WellAnnounced ms b
          → BlockOK ms (ev (evl (evLabel _ (apiLP l d lnpSendBlockAnnouncement) (header b))))
  ok-annP wa c-annP = wa

  ------------------------------------------------------------------------
  -- The five node-level threads
  ------------------------------------------------------------------------

  -- THE ANNOUNCEMENT GUARD AS AN EQUATION.  `forgeOK` is `⌊_⌋` of the very decision
  -- `NodeLogic.acceptForge` makes, so a `true` guard IS the seed's hypothesis.
  forgeOK-eq : ∀ (me : Maybe LeiosEb) (b : Block) → forgeOK (me , b) ≡ true
             → announcedEB b ≡ Data.Maybe.map ebHash me
  forgeOK-eq me b with announcedEB b ≟ Data.Maybe.map ebHash me
  ... | yes eq = λ _ → eq
  ... | no  _  = λ ()

  -- THE FORGE THREAD — the node's only forge route, and the only thread that DEPOSITS.
  -- The `envForge` value is unpinned (`blockOK-forge`), but under `forgeOK` the block is
  -- well-announced against the set the forge event itself grew, and that pays for the
  -- cert-RB's `stPut` three prefixes later.  (`BlockProvenanceNode.wf-forge` is vacuous
  -- and gives no template: `NodeLogic.forge` has no deposit.)
  wf-forgeL : ∀ {ms} n → Wf threadsGL ms (forgeL n)
  wf-forgeL n = wf-loop0 (wfR-Prefix (λ _ _ _ → blockOK-forge) pass)
    where
    -- the certificate half: the `stHasCert` rendezvous, then THIS THREAD'S own deposit.
    -- Both channels are CONCRETE, so `next` at them is the identity and no `next-⊇`
    -- step is wanted (see the comment at `AnnounceStoreL.wfR-offerHeldAt`).
    certHalf : ∀ {s} (b : Block) → WellAnnounced s b
             → WfR threadsGL s (λ _ _ → ⊤ {0ℓ}) (forgeCertL n b)
    certHalf b wa =
      wfR-maybe (rbCert b)
        (λ r → wfR-Prefix (λ _ _ _ ()) (λ le _ _ →
                 wfR-Output (λ le′ _ → ok-stPut (wellAnnounced-mono (⊆-trans le le′) wa))
                            (λ _ _ → wfR-Ret (λ _ → tt))))
        (wfR-Ret (λ _ → tt))
    -- one forge pass, at the state the forge event itself leads to
    pass : ∀ {s s′ : Forged} → s ⊆ s′ → ∀ mb → BlockOK s′ (lbl (forgeEv n) mb)
         → WfR threadsGL (next (lbl (forgeEv n) mb) s′) (λ _ _ → ⊤ {0ℓ}) (forgeBodyL n mb)
    pass {s′ = s′} le (me , b) _ =
      wfR-if (forgeOK (me , b))
        (λ eqOK →
           let wa = subst (λ xs → WellAnnounced xs b) (sym (next-forge (me , b) s′))
                          (forge-seed me b (forgeOK-eq me b eqOK))
           in wfR-maybe me
                (λ e → wfR-Output (λ _ _ ()) (λ le′ _ → certHalf b (wellAnnounced-mono le′ wa)))
                (certHalf b wa))
        (λ _ → wfR-Ret (λ _ → tt))

  -- THE EB INDEX THREAD: a read pointer over `held` whose only guarantee is at the
  -- EB-entry deposit, which carries no ranking block
  wf-ebIndex : ∀ {ms} n → Wf threadsGL ms (ebIndex n)
  wf-ebIndex n =
    wf-loop {body = ebIndexBody n} {a = 0} (λ _ _ _ → tt) (λ _ k _ → body k) tt
    where
    -- one pass: the read-pointer rely, then at most one `stPutEB`
    body : ∀ {s} (k : ℕ) → WfR threadsGL s (λ _ _ → ⊤ {0ℓ}) (ebIndexBody n k)
    body k =
      wfR-Prefix (λ _ _ g → ⊥-elim (proj₂ g)) (λ _ b _ →
        wfR-maybe (announcedEB b)
          (λ h → wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt)))
          (wfR-Ret (λ _ → tt)))

  -- THE VOTING THREAD: read pointer, body rendezvous, vote deposit — the vote blob is
  -- not a ranking block, so every guarantee is vacuous
  wf-voter : ∀ {ms} n → Wf threadsGL ms (voter n)
  wf-voter n =
    wf-loop {body = voterBody n} {a = 0} (λ _ _ _ → tt) (λ _ k _ → body k) tt
    where
    -- one pass of the voter
    body : ∀ {s} (k : ℕ) → WfR threadsGL s (λ _ _ → ⊤ {0ℓ}) (voterBody n k)
    body k =
      wfR-Prefix (λ _ _ g → ⊥-elim (proj₂ g)) (λ _ b _ →
        wfR-maybe (announcedEB b)
          (λ h → wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
                   wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt))))
          (wfR-Ret (λ _ → tt)))

  -- THE SUBMISSION THREAD: an `env` rendezvous and a mempool deposit, neither carried
  wf-submit : ∀ {ms} n → Wf threadsGL ms (submit n)
  wf-submit n =
    wf-loop0 (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
      wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt))))

  -- THE CERTIFICATE SINK: `stCert` carries an `RbHash`, not a block
  wf-certSink : ∀ {ms} n → Wf threadsGL ms (certSink n)
  wf-certSink n = wf-loop0 (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))

  ------------------------------------------------------------------------
  -- The sub-recursions of the per-endpoint threads
  ------------------------------------------------------------------------

  -- DEPOSIT EVERY CHECKED ENTRY of a tx-closure reply: structural on the entry list,
  -- and `stPutTx` carries no ranking block.  The `with` mirrors `putChecked`'s own.
  wfR-putChecked : ∀ n {ms} (h : EBHash) (es : List (ℕ × Tx))
                 → WfR threadsGL ms (λ _ _ → ⊤ {0ℓ}) (putChecked n h es)
  wfR-putChecked n h []             = wfR-Ret (λ _ → tt)
  wfR-putChecked n h ((o , e) ∷ es) with at? o (ebTxs h)
  ... | nothing      = wfR-putChecked n h es
  ... | just (k , _) =
    wfR-if ⌊ txHash e ≟ k ⌋
           (λ _ → wfR-Output (λ _ _ ()) (λ _ _ → wfR-putChecked n h es))
           (λ _ → wfR-putChecked n h es)

  -- deposit every delivered vote blob, in order
  wfR-putAllVotes : ∀ n {ms} (vs : List VoteBlob)
                  → WfR threadsGL ms (λ _ _ → ⊤ {0ℓ}) (putAllVotes n vs)
  wfR-putAllVotes n []       = wfR-Ret (λ _ → tt)
  wfR-putAllVotes n (v ∷ vs) = wfR-Output (λ _ _ ()) (λ _ _ → wfR-putAllVotes n vs)

  -- deposit every REQUESTED transaction pulled off the wire: the membership guard, whose
  -- Boolean is written out because `wfR-if _ p q` does not unify (ledger gotcha), and
  -- whose two arms are both well-formed since the guard only drops a deposit
  wfR-putAllTx : ∀ n {ms} (ids : List TxHash) (ts : List Tx)
               → WfR threadsGL ms (λ _ _ → ⊤ {0ℓ}) (putAllTx n ids ts)
  wfR-putAllTx n ids []       = wfR-Ret (λ _ → tt)
  wfR-putAllTx n ids (e ∷ es) =
    wfR-if (memberOf (txHash e) ids)
           (λ _ → wfR-Output (λ _ _ ()) (λ _ _ → wfR-putAllTx n ids es))
           (λ _ → wfR-putAllTx n ids es)

  -- fetch an offered EB body: the request, the reply and the hash-checked deposit
  wfR-fetchBody : ∀ n l d {ms} (q : EBHash × LSlot) (sz : Size)
                → WfR threadsGL ms (λ _ _ → ⊤ {0ℓ}) (fetchBody n l d (q , sz))
  wfR-fetchBody n l d q sz =
    wfR-Output ⦃ DecEq-EBPoint ⦄ (λ _ _ ()) (λ _ _ →
      wfR-Prefix (λ _ _ _ ()) (λ _ eb _ →
        wfR-if ⌊ ebHash eb ≟ proj₁ q ⌋
               (λ _ → wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt)))
               (λ _ → wfR-Ret (λ _ → tt))))

  -- fetch the whole tx closure of an offered point: block at the body, request every
  -- offset, check the echoed point, then deposit
  wfR-fetchTxs : ∀ n l d {ms} (q : EBHash × LSlot)
               → WfR threadsGL ms (λ _ _ → ⊤ {0ℓ}) (fetchTxs n l d q)
  wfR-fetchTxs n l d q =
    wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
      wfR-Output ⦃ DecEq-TxsRequest ⦄ (λ _ _ ()) (λ _ _ →
        wfR-Prefix (λ _ _ _ ()) (λ { _ (q′ , es) _ →
          wfR-if ⌊ DecEq-EBPoint ._≟_ q′ q ⌋
                 (λ _ → wfR-putChecked n (proj₁ q) es) (λ _ → wfR-Ret (λ _ → tt)) })))

  -- SERVE THE REQUESTED OFFSETS: structural on the bitmap, and neither the keyed
  -- mempool read nor the reply carries a ranking block.  The `with` mirrors `serveTxs`'s.
  wfR-serveTxs : ∀ n l d {ms} (q : EBHash × LSlot) (bm : TxBitmap) (acc : List (ℕ × Tx))
               → WfR threadsGL ms (λ _ _ → ⊤ {0ℓ}) (serveTxs n l d q bm acc)
  wfR-serveTxs n l d q []       acc =
    wfR-Output ⦃ DecEq-TxsReply ⦄ (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt))
  wfR-serveTxs n l d q (o ∷ os) acc with at? o (ebTxs (proj₁ q))
  ... | nothing      = wfR-serveTxs n l d q os acc
  ... | just (h , _) =
    wfR-Prefix (λ _ _ _ ()) (λ _ e _ → wfR-serveTxs n l d q os (acc ++ ((o , e) ∷ [])))

  ------------------------------------------------------------------------
  -- The ten per-endpoint threads
  ------------------------------------------------------------------------

  -- THE PRAOS CLIENT: `NodeLogic.clientLoop` verbatim, so `BlockProvenanceNode`'s fact
  -- transfers — `threadsGL ⊆ threadsG` is `proj₁`, which is why `threadsGL` is a product
  wf-clientLoopL : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (clientLoop n ld)
  wf-clientLoopL n ld = wf-mono-G (λ _ _ → proj₁) (wf-clientLoop n ld)

  -- THE PRAOS SERVER: relies at the READ POINTER (excluded from `threadsGL`) and serves
  -- that block at `apiBF … sendBFBlock` five prefixes later.  This is why `c-stGetAt`
  -- was added; the tail is `BlockProvenanceNode.wf-serverLoop`'s own continuation,
  -- re-derived because it is `where`-bound there.
  wf-serverLoopL : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (serverLoopL n ld)
  wf-serverLoopL n (l , d) =
    wf-loop {body = serverBodyL n l (opposite d)} {a = 0}
            (λ _ _ _ → tt) (λ _ k _ → body k) tt
    where
    -- the tail of a server round on a well-announced block
    serverTail : ∀ {s} (b : Block) → WellAnnounced s b
               → WfR threadsGL s (λ _ _ → ⊤ {0ℓ}) (serverBody-k n l (opposite d) b)
    serverTail b wa =
      wfR-Prefix (λ _ _ _ → blockOK-apiCS) (λ le₁ _ _ →
      wfR-Output (λ _ _ → blockOK-apiCS) (λ le₂ _ →
      wfR-Prefix (λ _ _ _ → blockOK-bfReq) (λ le₃ _ _ →
      wfR-Prefix (λ _ _ _ → blockOK-bfStart) (λ le₄ _ _ →
      wfR-Output (λ le₅ _ → ok-sendBF (wellAnnounced-mono
                     (⊆-trans le₁ (⊆-trans le₂ (⊆-trans le₃ (⊆-trans le₄ le₅)))) wa)) (λ _ _ →
      wfR-Prefix (λ _ _ _ → blockOK-bfDone) (λ _ _ _ → wfR-Ret (λ _ → tt)))))))
    -- one server round: the far end's RequestNext, the read pointer, then the tail
    body : ∀ {s} (k : ℕ) → WfR threadsGL s (λ _ _ → ⊤ {0ℓ}) (serverBodyL n l (opposite d) k)
    body k =
      wfR-Prefix (λ _ _ _ → blockOK-apiCS) (λ _ _ _ →
        wfR-Prefix (λ _ _ g → ⊥-elim (proj₂ g)) (λ _ b ok →
          wfR->>= (serverTail b (ok c-stGetAt)) (λ _ _ _ → wfR-Ret (λ _ → tt))))

  -- THE ANNOUNCE LEAF, and the whole point of S0: relies at the READ POINTER and
  -- announces that block's header on the PROTOTYPE channel one prefix later
  wf-lnServerLoopL : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (lnServerLoopL n ld)
  wf-lnServerLoopL n (l , d) =
    wf-loop {body = lnServerBodyL n l (opposite d)} {a = 0}
            (λ _ _ _ → tt) (λ _ k _ → body k) tt
    where
    -- one announce round
    body : ∀ {s} (k : ℕ) → WfR threadsGL s (λ _ _ → ⊤ {0ℓ}) (lnServerBodyL n l (opposite d) k)
    body k =
      wfR-Prefix (λ _ _ g → ⊥-elim (proj₂ g)) (λ _ b ok →
        wfR-Output (λ le′ _ → ok-annP (wellAnnounced-mono le′ (ok c-stGetAt)))
                   (λ _ _ → wfR-Ret (λ _ → tt)))

  -- THE ONE NOTIFY CLIENT: a long-poll request and a four-way `□` of STABLE prefixes,
  -- none of whose `apiLP` channels carries a ranking block
  wf-lnClientLoopL : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (lnClientLoopL n ld)
  wf-lnClientLoopL n (l , d) =
    wf-loop0 (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
      wfR-□ _ _ (stable-node refl)
        (stable-□ (stable-node refl) (stable-□ (stable-node refl) (stable-node refl)))
        (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
        (wfR-□ _ _ (stable-node refl) (stable-□ (stable-node refl) (stable-node refl))
          (wfR-Prefix (λ _ _ _ ()) (λ { _ (q , sz) _ → wfR-fetchBody n l d q sz }))
          (wfR-□ _ _ (stable-node refl) (stable-node refl)
            (wfR-Prefix (λ _ _ _ ()) (λ _ q _ → wfR-fetchTxs n l d q))
            (wfR-Prefix (λ _ _ _ ()) (λ _ vs _ → wfR-putAllVotes n vs))))))

  -- THE TX-CLOSURE GATE: mempool reads only, which `Carries` does not name, so any
  -- state-polymorphic witness of the continuation passes straight through
  wfR-awaitTxs : ∀ n {ms} (hs : List (TxHash × Size))
                   {P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ}
               → (∀ {ms′} → WfR threadsGL ms′ (λ _ _ → ⊤ {0ℓ}) P)
               → WfR threadsGL ms (λ _ _ → ⊤ {0ℓ}) (awaitTxs n hs P)
  wfR-awaitTxs n []             wP = wP
  wfR-awaitTxs n ((h , _) ∷ hs) wP =
    wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-awaitTxs n hs wP)

  -- THE BODY-OFFER THREAD: a read pointer, the body rendezvous and two `apiLP` offers,
  -- which carry a POINT and a SIZE, never a ranking block
  wf-bodyOfferLoop : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (bodyOfferLoop n ld)
  wf-bodyOfferLoop n (l , d) =
    wf-loop {body = bodyOfferBody n l (opposite d)} {a = 0}
            (λ _ _ _ → tt) (λ _ k _ → body k) tt
    where
    -- one body-offer round
    body : ∀ {s} (k : ℕ) → WfR threadsGL s (λ _ _ → ⊤ {0ℓ}) (bodyOfferBody n l (opposite d) k)
    body k =
      wfR-Prefix (λ _ _ g → ⊥-elim (proj₂ g)) (λ _ b _ →
        wfR-maybe (announcedEB b)
          (λ h → wfR-Prefix (λ _ _ _ ()) (λ _ eb _ →
                   wfR-Output ⦃ DecEq-Offer ⦄ (λ _ _ ()) (λ _ _ →
                     wfR-awaitTxs n (ebTxs h)
                       (wfR-Output ⦃ DecEq-EBPoint ⦄ (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt))))))
          (wfR-Ret (λ _ → tt)))

  -- THE VOTE-OFFER THREAD: the vote store's read pointer carries a blob, which
  -- `Carries` does not name, so both ends are vacuous
  wf-voteOfferLoop : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (voteOfferLoop n ld)
  wf-voteOfferLoop n (l , d) =
    wf-loop {body = voteOfferBody n l (opposite d)} {a = 0}
            (λ _ _ _ → tt)
            (λ _ k _ → wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
                         wfR-Output ⦃ DecEqI.DecEq-List ⦄ (λ _ _ ())
                                    (λ _ _ → wfR-Ret (λ _ → tt))))
            tt

  -- THE EB-SERVE THREAD: a point request, the body rendezvous and the body on the wire
  wf-ebServeLoop : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (ebServeLoop n ld)
  wf-ebServeLoop n (l , d) =
    wf-loop0 (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
      wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
        wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt)))))

  -- THE TX-CLOSURE-SERVE THREAD: the request, the body rendezvous, then `serveTxs`
  wf-ebTxsServeLoop : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (ebTxsServeLoop n ld)
  wf-ebTxsServeLoop n (l , d) =
    wf-loop0 (wfR-Prefix (λ _ _ _ ()) (λ { _ (q , bm) _ →
      wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
        wfR-serveTxs n l (opposite d) q bm []) }))

  -- THE TXSUBMISSION PULL THREAD: four `apiTS` events and a deposit list
  wf-tsPull : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (tsPull n ld)
  wf-tsPull n (l , d) =
    wf-loop0 (wfR-Output (λ _ _ ()) (λ _ _ →
      wfR-Prefix (λ _ _ _ ()) (λ _ ids _ →
        wfR-Output ⦃ DecEqI.DecEq-List ⦄ (λ _ _ ()) (λ _ _ →
          wfR-Prefix (λ _ _ _ ()) (λ _ ts _ → wfR-putAllTx n ids ts)))))

  -- THE TXSUBMISSION SERVE THREAD: a read pointer over the mempool, which carries a
  -- transaction, not a ranking block
  wf-tsServe : ∀ {ms} n (ld : Link × Dir) → Wf threadsGL ms (tsServe n ld)
  wf-tsServe n (l , d) =
    wf-loop {body = tsServeBody n l d} {a = 0} (λ _ _ _ → tt) (λ _ k _ → body k) tt
    where
    -- one serve round
    body : ∀ {s} (k : ℕ) → WfR threadsGL s (λ _ _ → ⊤ {0ℓ}) (tsServeBody n l d k)
    body k =
      wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
        wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
          wfR-Output ⦃ DecEqI.DecEq-List ⦄ (λ _ _ ()) (λ _ _ →
            wfR-Prefix (λ _ _ _ ()) (λ _ _ _ →
              wfR-Output ⦃ DecEqI.DecEq-List ⦄ (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt))))))

  ------------------------------------------------------------------------
  -- The thread group, and the node
  ------------------------------------------------------------------------

  -- one endpoint's ten threads, in `endpointThreadsL`'s own order
  wf-endpointThreadsL : ∀ {ms} n (e : Link × Dir) → Wf threadsGL ms (endpointThreadsL n e)
  wf-endpointThreadsL n e =
    wf-⦀ (wf-clientLoopL n e)
      (wf-⦀ (wf-serverLoopL n e)
      (wf-⦀ (wf-lnClientLoopL n e)
      (wf-⦀ (wf-lnServerLoopL n e)
      (wf-⦀ (wf-bodyOfferLoop n e)
      (wf-⦀ (wf-voteOfferLoop n e)
      (wf-⦀ (wf-ebServeLoop n e)
      (wf-⦀ (wf-ebTxsServeLoop n e)
      (wf-⦀ (wf-tsPull n e) (wf-tsServe n e)))))))))

  -- every incident endpoint's ten, interleaved in `endpointsOf`'s order
  wf-allThreadsL : ∀ {ms} n → Wf threadsGL ms (allThreadsL n)
  wf-allThreadsL n =
    wf-⦀⁺ (endpointThreadsL n) (proj₁ (endpointsOf n)) (proj₂ (endpointsOf n))
          (wf-endpointThreadsL n)

  -- THE FIVE NODE-LEVEL THREADS and every endpoint's ten, all on `threadsGL` — the left
  -- operand of the node's `∥⇘ storeES ⇙`
  wf-threadsL : ∀ {ms} n → Wf threadsGL ms
                  (forgeL n ⦀ (ebIndex n ⦀ (voter n ⦀ (submit n ⦀
                     (certSink n ⦀ allThreadsL n)))))
  wf-threadsL n =
    wf-⦀ (wf-forgeL n)
      (wf-⦀ (wf-ebIndex n)
      (wf-⦀ (wf-voter n)
      (wf-⦀ (wf-submit n)
      (wf-⦀ (wf-certSink n) (wf-allThreadsL n)))))

  -- S0, AT THE NODE: the whole Linear-Leios node logic is well-formed on `nodeG`
  -- whenever its RB store holds only well-announced blocks.  The two halves meet at
  -- `storeES` under `sep-storeL`, and `nodeG⊆` shrinks the union back to `nodeG`.
  wf-nodeLogicL : ∀ {ms} n {held : Held} {es : Entries} {bs : Bodies} {ts : Mem} {vs : Votes}
                → StoreInv ms held
                → Wf nodeG ms (nodeLogicL n (held , es , bs , ts , vs))
  wf-nodeLogicL n {es = es} {bs = bs} {ts = ts} {vs = vs} inv =
    wf-mono-G nodeG⊆
      (wf-Par storeES sep-storeL (wf-threadsL n) (wf-storesL n es bs ts vs inv))

  ------------------------------------------------------------------------
  -- Non-vacuity: both announce channels are in the threads' alphabet
  ------------------------------------------------------------------------

  -- so `wf→gate` applies to `wf-lnServerLoopL`, to `wf-threadsL` and to `wf-nodeLogicL`
  annIn-threadsGL : AnnIn threadsGL
  annIn-threadsGL annLN = tt , tt
  annIn-threadsGL annLP = tt , tt

  -- …and to the node, whose alphabet is `nodeG`
  annIn-nodeG : AnnIn nodeG
  annIn-nodeG annLN = tt
  annIn-nodeG annLP = tt

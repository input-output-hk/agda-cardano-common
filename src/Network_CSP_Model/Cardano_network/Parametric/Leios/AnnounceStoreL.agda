{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — ANNOUNCEMENT SAFETY AT `nodeLogicL`'s FIVE
-- STORES: the store half of the S0 leaf layer, in the ANNOUNCE discipline
-- (`Parametric.BlockProvenance`'s `Carries`/`WellAnnounced`/`next`).
--
-- This is the `nodeLogicL` counterpart of `BlockProvenanceNode.agda:144-255`
-- and structurally the `CertSound.agda:376-640` store block re-instantiated
-- on the announce carrier instead of the certificate one.  Nothing in
-- `NodeLogicL.agda` is touched.
--
-- WHAT IS REUSED RATHER THAN REBUILT.  The announce discipline's alphabets
-- and their `Sep` already exist and are already right for `nodeLogicL`:
-- `BlockProvenanceNode.nodeG`/`storeG`/`threadsG` and
-- `AnnounceSafeCopy.sep-store`.  `nodeLogicL` adds no block-carrying rely
-- and no block-carrying guarantee beyond `NodeLogic`'s (`Carries` names
-- `stGet` and `stPut`, and the four new stores' channels carry no `Block`),
-- so `storeG` is unchanged and needs no `storeGL` of its own — the alphabet
-- layer of S0 costs nothing.  `StoreInv`, `storeInv-mono`, `forge-seed`,
-- `acceptForge-wa`, `stable-offerHeld`, `offerHeld-wf`, `ok-stGet`,
-- `ok-stPut` are likewise imported from `BlockProvenanceNode.Generic` at the
-- same three parameters and the same carrier instance.
--
-- THE `putEv` BRANCH IS THE RELY, NOT A PREMISE.  `storeStepL`'s deposit arm
-- is ungated by design (the wire route needs it) and cannot be discharged
-- node-locally.  `WfR`'s `stepR` hands the label's own `BlockOK` over, and at
-- `store … stPut` that IS `WellAnnounced ms b` (`c-stPut`), so the unguarded
-- deduped deposit is fine and the network-wide argument is the assembly's, exactly
-- as `BlockProvenanceNode.storeBody` has it.  Nothing here is weakened and
-- nothing is postulated.
--
-- `stGetAt` CARRIES THE BLOCK IT HANDS OUT.  `BlockProvenance.Carries` now
-- has `c-stGetAt` beside `c-stGet`, so the read-pointer menu
-- `offerIx (getAtEv n) (reverse held) 0 held` owes a REAL guarantee: each
-- operand must offer a well-announced block.  It is paid elementwise from
-- `StoreInv` — transported across the menu's own `reverse` by `all-reverse`
-- — which is why `wfR-offerHeldAt` below replaces what used to be a vacuous
-- `wfR-offerIx` application.  The four content-free stores keep the vacuous
-- lemma: `stGetEBAt`/`stGetTxAt`/`stGetVoteAt` are other `StoreTag`s and
-- `c-stGetAt` does not unify with them.
--
-- The arm exists for the THREAD half's sake: `lnServerBodyL`/`serverBodyL`/
-- `voterBody`/`bodyOfferBody`/`ebIndexBody` all read a block through
-- `stGetAt`, and `serverLoopL` then emits it on `apiBF … sendBFBlock`, which
-- `Carries` DOES name — so without a rely at `stGetAt` that guarantee could
-- not be discharged at all.
--
-- Also note: `nodeLogicL` announces on `apiLP … lnpSendBlockAnnouncement`,
-- and `AnnounceSpecT` now GATES that channel (`AnnEv`'s `annLP`, beside the
-- `apiLN` channel `nodeLogic` uses), so announcement safety of
-- `systemOfWithNode (nodeWith nodeBundleP) …` has content.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.AnnounceStoreL where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; reverse)
open import Data.List.Properties using (unfold-reverse)
import Data.List.Relation.Unary.All as All
open All using (All)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Class.DecEq using (DecEq)
open import Class.DecEq.Instances using (DecEq-List)

open import Process_Trees using (AnyTypes; ExtI)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Topology using (Topology)
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

-- the announce discipline at `nodeLogicL`'s stores, parametric in the same five
-- arguments `NodeLogicL.Generic` takes, so the stores below are literally its terms
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open Params p
    using ( Block; LSlot; VoteBlob; EB; EBHash; RbHash; Tx; TxHash
          ; ebHash; rbHash; txHash; announcedEB
          ; decBlock; decEBHash; decLSlot; decVoteBlob; decEB
          ; decRbHash; decTx; decTxHash )
  open LeiosP p using (LeiosEb; LeiosPoint; DecEq-LeiosPoint)
  open LeiosP.LeiosParams lp using (rbCert; blobRb; certifies)
  open N p
    using ( Link; Net_Api; Net_Api-≟; store; env
          ; stPut; stGet; stGetAt; stPutEB; stGetEBAt; stPutBody; stGetBody
          ; stPutTx; stGetTxAt; stGetTx; stPutVote; stGetVoteAt; stCert; stHasCert
          ; envForge; envSubmit )
  -- `Data.DecEq-Tx` is deliberately NOT opened, so `decTx` is the ONE `DecEq Tx` in
  -- scope and instance search resolves the very term `NodeLogicL` used
  open D p using (Payload)
  open Topology t using (Node)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (EventSet; _⦀_)
  open import Cardano_network.Parametric.Node p t apiES using (Proc)
  open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; √; evLabel)
  open NL.Generic p t apiES
    using (Held; StoreProc; homeOf; forgeEv; putEv; getEv; offerHeld; acceptForge)
  open NLL.Generic p lp t apiES voterOf
    using ( DecEq-⊤poly; DecEq-Votes
          ; Entries; Bodies; Mem; Blobs; Certs; Votes; StateL
          ; memberOf; offerIx; acceptForgeL
          ; getAtEv; putEBEv; getEBAtEv; putBodyEv; getBodyEv
          ; putTxEv; getTxAtEv; getTxEv; putVoteEv; getVoteAtEv
          ; certEv; hasCertEv; submitEv
          ; storeStepL; blockStoreL; ebStep; ebStore; bodyStep; offerBodies; bodyStore
          ; memStep; offerTxs; mempool; certify; offerCerts; voteStep; voteStore )
  open AS.Generic p t apiES using (Forged)
  open AI.Generic p t apiES using (WellAnnounced; wellAnnounced-mono)
  -- the announce carrier, wholesale (`Carries`, `next`, `next-⊇`, `BlockOK`, `Wf`, …)
  open BP.Generic p t apiES
  -- … and its returning-tree layer at exactly the arguments `BlockProvenanceNode`
  -- opened it with, so the two `Wf`/`WfR` records are the same records
  open BPW.Body (Net_Api-≟ {Payload}) Forged Block Carries WellAnnounced
            next _⊆_ ⊆-refl ⊆-trans next-⊇
  -- THE ALPHABETS AND THE RB-STORE LEAVES ARE ALREADY BUILT: `nodeLogicL` adds no
  -- block-carrying channel, so `BlockProvenanceNode`'s node/store alphabets and the
  -- whole `offerHeld`/`acceptForge` layer transfer verbatim (module header)
  open BPN.Generic p t apiES
    using ( nodeG; storeG; threadsG; StoreInv; storeInv-mono; forge-seed
          ; acceptForge-wa; stable-offerHeld; offerHeld-wf; ok-stGet; ok-stPut )

  ------------------------------------------------------------------------
  -- The read-pointer menu of design law L
  ------------------------------------------------------------------------

  -- a read-pointer menu is stable: every operand is a bare output and `Stop` is a
  -- `react` with no τ.  (Copied out of `CertSound.Generic`, which is parameterised on
  -- the certificate discipline and so cannot be opened here; the alternative was to
  -- hoist it above both modules, which would have touched `CertSound`.)
  stable-offerIx : ∀ {A St : Set} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq St ⦄
                     (ch : ℕ → Net_Api Payload A) (xs : List A) (k : ℕ) (st : St)
                 → Stable (offerIx ch xs k st)
  stable-offerIx ch []       k st = stable-node refl
  stable-offerIx ch (x ∷ xs) k st =
    stable-□ (stable-node refl) (stable-offerIx ch xs (suc k) st)

  -- … and well-formed whenever none of its channels carries a block, since it hands
  -- back the state it was given.  THE FOUR CONTENT-FREE STORES ARE THE VACUOUS CASES:
  -- `Carries` names `stGetAt`, but not `stGetEBAt`/`stGetTxAt`/`stGetVoteAt`.  The RB
  -- store's own menu pays a real guarantee — see `wfR-offerHeldAt` (module header).
  wfR-offerIx : ∀ {A St : Set} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq St ⦄
                  {Inv : Forged → St → Set} {ms}
                  (ch : ℕ → Net_Api Payload A) (xs : List A) (k : ℕ) (st : St)
              → (∀ i (x : A) {b} → Carries (A , ch i) x b → ⊥)
              → (∀ {s₁ s₂} → s₁ ⊆ s₂ → Inv s₁ st → Inv s₂ st)
              → Inv ms st
              → WfR storeG ms Inv (offerIx ch xs k st)
  wfR-offerIx ch []       k st free mono inv = wfR-Stop
  wfR-offerIx ch (x ∷ xs) k st free mono inv =
    wfR-□ _ _ (stable-node refl) (stable-offerIx ch xs (suc k) st)
      (wfR-Output (λ _ _ c → ⊥-elim (free k x c))
                  (λ le _ → wfR-Ret (λ le′ →
                     mono (⊆-trans le (⊆-trans (next-⊇ _ _) le′)) inv)))
      (wfR-offerIx ch xs (suc k) st free mono inv)

  ------------------------------------------------------------------------
  -- The RB store: the one content-bearing leaf
  ------------------------------------------------------------------------

  -- `acceptForgeL` keeps the invariant.  A certificate-carrying block is WITHHELD, so
  -- `held` is untouched and plain monotonicity pays; a certificate-free one goes through
  -- `NodeLogic.acceptForge`, whose guard IS the seed (`acceptForge-wa`, `forge-seed`).
  acceptForgeL-wa : ∀ n {ms held} (me : Maybe LeiosEb) (b : Block) → StoreInv ms held
                  → ∀ {ms′} → next (lbl (forgeEv n) (me , b)) ms ⊆ ms′
                  → StoreInv ms′ (acceptForgeL (me , b) held)
  acceptForgeL-wa n {ms} me b inv le with rbCert b
  ... | just _  = storeInv-mono (⊆-trans (next-⊇ _ ms) le) inv
  ... | nothing = acceptForge-wa n me b inv le

  -- `All` survives `reverse`.  The read-pointer menu enumerates `reverse held` (design
  -- law L offers the OLDEST block at index 0), so the store's invariant has to be
  -- transported across the reversal; stdlib has no `All` reverse lemma, and
  -- `unfold-reverse` plus `All.++⁺` is the whole proof.
  all-reverse : ∀ {P : Block → Set} {xs : Held} → All P xs → All P (reverse xs)
  all-reverse All.[] = All.[]
  all-reverse {P = P} {xs = x ∷ xs} (px All.∷ pxs) =
    subst (All P) (sym (unfold-reverse x xs))
          (AllP.++⁺ (all-reverse pxs) (px All.∷ All.[]))

  -- `All` survives the RB store's DEDUP deposit: `held` is either kept or has `b` prepended
  all-dedup : ∀ {P : Block → Set} {xs : Held} {b : Block} (c : Bool)
            → All P xs → P b → All P (if c then xs else b ∷ xs)
  all-dedup true  pxs pb = pxs
  all-dedup false pxs pb = pb All.∷ pxs

  -- THE READ-POINTER MENU OF THE RB STORE, with content.  `c-stGetAt` makes each
  -- operand's output a guarantee, discharged by the well-announcedness of the very
  -- block that operand offers — so this takes the invariant ELEMENTWISE where the
  -- content-free stores' `wfR-offerIx` takes a `Carries` refutation.
  wfR-offerHeldAt : ∀ n {ms held} (xs : Held) (k : ℕ)
                  → All (WellAnnounced ms) xs → StoreInv ms held
                  → WfR storeG ms StoreInv (offerIx (getAtEv n) xs k held)
  wfR-offerHeldAt n []       k was inv = wfR-Stop
  wfR-offerHeldAt n {held = held} (x ∷ xs) k (wa All.∷ was) inv =
    wfR-□ _ _ (stable-node refl) (stable-offerIx (getAtEv n) xs (suc k) held)
      -- no `next-⊇` step here, unlike `wfR-offerIx`: the channel is CONCRETE, so
      -- `forgeOf` reduces on its label and `next` at a read is the identity
      (wfR-Output (λ le _ → λ { c-stGetAt → wellAnnounced-mono le wa })
                  (λ le _ → wfR-Ret (λ le′ → storeInv-mono (⊆-trans le le′) inv)))
      (wfR-offerHeldAt n xs (suc k) was inv)

  -- ONE RB-STORE PASS, four branches (`76bb8ec2` deleted the fifth, the cert-forge arm).
  -- The forge: an `env` channel, so `BlockOK` is vacuous and the invariant is restored by
  -- `acceptForgeL-wa`.  The deposit: THE RELY — `stepR` hands over `BlockOK ms (stPut ! b)`,
  -- which is `WellAnnounced ms b`, so the ungated, deduped deposit is fine.  The legacy menu: the
  -- `stGet` guarantee, `offerHeld-wf`.  The read-pointer menu: the `stGetAt` guarantee,
  -- `wfR-offerHeldAt`, paid from `StoreInv` through `all-reverse`.
  storeBodyL : ∀ n {ms held} → StoreInv ms held → WfR storeG ms StoreInv (storeStepL n held)
  storeBodyL n {held = held} inv =
    wfR-□ _ _ (stable-node refl)
      (stable-□ (stable-node refl)
        (stable-□ (stable-offerHeld n held held)
                  (stable-offerIx (getAtEv n) (reverse held) 0 held)))
      (wfR-Prefix (λ _ _ _ → blockOK-forge)
                  (λ le mb _ → wfR-Ret (acceptForgeL-wa n (proj₁ mb) (proj₂ mb)
                                          (storeInv-mono le inv))))
      (wfR-□ _ _ (stable-node refl)
        (stable-□ (stable-offerHeld n held held)
                  (stable-offerIx (getAtEv n) (reverse held) 0 held))
        (wfR-Prefix (λ _ _ g → ⊥-elim g)
                    (λ le b ok → wfR-Ret (λ le′ →
                       all-dedup (memberOf b held) (storeInv-mono (⊆-trans le le′) inv)
                                 (wellAnnounced-mono le′ (ok c-stPut)))))
        (wfR-□ _ _ (stable-offerHeld n held held)
                   (stable-offerIx (getAtEv n) (reverse held) 0 held)
          (offerHeld-wf n inv held inv)
          (wfR-offerHeldAt n (reverse held) 0 (all-reverse inv) inv)))

  -- THE RB STORE: well-formed on `storeG` whenever what it holds is well-announced
  wf-blockStoreL : ∀ {ms held} n → StoreInv ms held → Wf storeG ms (blockStoreL n held)
  wf-blockStoreL n inv = wf-loop (λ le _ → storeInv-mono le) (λ _ _ → storeBodyL n) inv

  ------------------------------------------------------------------------
  -- The four stores that carry no block — vacuous, and shown so
  ------------------------------------------------------------------------

  -- the EB-entry store: a deposit on `stPutEB` and a read-pointer menu on `stGetEBAt`,
  -- neither of which `Carries` names
  wf-ebStore : ∀ {ms} n (es : Entries) → Wf storeG ms (ebStore n es)
  wf-ebStore n es =
    wf-loop {body = ebStep n} {a = es} (λ _ _ _ → tt) (λ _ xs _ → body xs) tt
    where
    -- one pass of the EB-entry store
    body : ∀ {s} (xs : Entries) → WfR storeG s (λ _ _ → ⊤ {0ℓ}) (ebStep n xs)
    body xs =
      wfR-□ _ _ (stable-node refl) (stable-offerIx (getEBAtEv n) xs 0 xs)
        (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
        (wfR-offerIx (getEBAtEv n) xs 0 xs (λ _ _ ()) (λ _ _ → tt) tt)

  -- the EB-body store's by-hash menu is stable …
  stable-offerBodies : ∀ n (bs ebs : Bodies) → Stable (offerBodies n bs ebs)
  stable-offerBodies n bs []         = stable-node refl
  stable-offerBodies n bs (eb ∷ ebs) =
    stable-□ (stable-node refl) (stable-offerBodies n bs ebs)

  -- … and carries nothing: `stGetBody h` is neither `stGet` nor `stPut`
  wfR-offerBodies : ∀ {ms} n (bs ebs : Bodies)
                  → WfR storeG ms (λ _ _ → ⊤ {0ℓ}) (offerBodies n bs ebs)
  wfR-offerBodies n bs []         = wfR-Stop
  wfR-offerBodies n bs (eb ∷ ebs) =
    wfR-□ _ _ (stable-node refl) (stable-offerBodies n bs ebs)
      (wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt)))
      (wfR-offerBodies n bs ebs)

  -- the EB-body store: a deposit and the by-hash menu
  wf-bodyStore : ∀ {ms} n (bs : Bodies) → Wf storeG ms (bodyStore n bs)
  wf-bodyStore n bs =
    wf-loop {body = bodyStep n} {a = bs} (λ _ _ _ → tt) (λ _ xs _ → body xs) tt
    where
    -- one pass of the EB-body store
    body : ∀ {s} (xs : Bodies) → WfR storeG s (λ _ _ → ⊤ {0ℓ}) (bodyStep n xs)
    body xs =
      wfR-□ _ _ (stable-node refl) (stable-offerBodies n xs xs)
        (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
        (wfR-offerBodies n xs xs)

  -- the mempool's by-hash menu is stable …
  stable-offerTxs : ∀ n (ts us : Mem) → Stable (offerTxs n ts us)
  stable-offerTxs n ts []         = stable-node refl
  stable-offerTxs n ts (tx′ ∷ us) =
    stable-□ (stable-node refl) (stable-offerTxs n ts us)

  -- … and carries nothing either
  wfR-offerTxs : ∀ {ms} n (ts us : Mem)
               → WfR storeG ms (λ _ _ → ⊤ {0ℓ}) (offerTxs n ts us)
  wfR-offerTxs n ts []         = wfR-Stop
  wfR-offerTxs n ts (tx′ ∷ us) =
    wfR-□ _ _ (stable-node refl) (stable-offerTxs n ts us)
      (wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt)))
      (wfR-offerTxs n ts us)

  -- the mempool: a deposit, THE SUBMISSION RENDEZVOUS (an `env` channel, so vacuous), a
  -- read-pointer menu and the by-hash menu
  wf-mempool : ∀ {ms} n (ts : Mem) → Wf storeG ms (mempool n ts)
  wf-mempool n ts =
    wf-loop {body = memStep n} {a = ts} (λ _ _ _ → tt) (λ _ xs _ → body xs) tt
    where
    -- one pass of the mempool
    body : ∀ {s} (xs : Mem) → WfR storeG s (λ _ _ → ⊤ {0ℓ}) (memStep n xs)
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

  -- the certificate menu is stable …
  stable-offerCerts : ∀ n (vs : Votes) (rs : Certs) → Stable (offerCerts n vs rs)
  stable-offerCerts n vs []       = stable-node refl
  stable-offerCerts n vs (r ∷ rs) =
    stable-□ (stable-node refl) (stable-offerCerts n vs rs)

  -- … and carries nothing: `stHasCert r` is value-free
  wfR-offerCerts : ∀ {ms} n (vs : Votes) (rs : Certs)
                 → WfR storeG ms (λ _ _ → ⊤ {0ℓ}) (offerCerts n vs rs)
  wfR-offerCerts n vs []       = wfR-Stop
  wfR-offerCerts n vs (r ∷ rs) =
    wfR-□ _ _ (stable-node refl) (stable-offerCerts n vs rs)
      (wfR-Prefix (λ _ _ _ ()) (λ _ _ _ → wfR-Ret (λ _ → tt)))
      (wfR-offerCerts n vs rs)

  -- the certification firing: `stCert` carries an `RbHash`, not a block, so both sides
  -- of the Boolean guard are vacuous here
  wfR-certify : ∀ n {ms} (bs : Blobs) (cs : Certs) (r : RbHash)
              → WfR storeG ms (λ _ _ → ⊤ {0ℓ}) (certify n bs cs r)
  wfR-certify n bs cs r with certifies bs r ∧ not (memberOf r cs)
  ... | false = wfR-Ret (λ _ → tt)
  ... | true  = wfR-Output (λ _ _ ()) (λ _ _ → wfR-Ret (λ _ → tt))

  -- the vote store: a deposit that consults the oracle, a read-pointer menu and the
  -- certificate menu
  wf-voteStore : ∀ {ms} n (vs : Votes) → Wf storeG ms (voteStore n vs)
  wf-voteStore n vs =
    wf-loop {body = voteStep n} {a = vs} (λ _ _ _ → tt) (λ _ xs _ → body xs) tt
    where
    -- one pass of the vote store
    body : ∀ {s} (xs : Votes) → WfR storeG s (λ _ _ → ⊤ {0ℓ}) (voteStep n xs)
    body (bs , cs) =
      wfR-□ _ _ (stable-node refl)
        (stable-□ (stable-offerIx (getVoteAtEv n) bs 0 (bs , cs))
                  (stable-offerCerts n (bs , cs) cs))
        (wfR-Prefix (λ _ _ _ ()) (λ _ v _ → wfR-certify n _ cs _))
        (wfR-□ _ _ (stable-offerIx (getVoteAtEv n) bs 0 (bs , cs))
                   (stable-offerCerts n (bs , cs) cs)
          (wfR-offerIx (getVoteAtEv n) bs 0 (bs , cs) (λ _ _ ()) (λ _ _ → tt) tt)
          (wfR-offerCerts n (bs , cs) cs))

  ------------------------------------------------------------------------
  -- The store group
  ------------------------------------------------------------------------

  -- THE FIVE STORES of `nodeLogicL`, interleaved in the order `nodeLogicL` writes them,
  -- all on `storeG` — the right operand of the node's `∥⇘ storeES ⇙`, ready for
  -- `wf-Par storeES AnnounceSafeCopy.sep-store` once the thread half exists
  wf-storesL : ∀ {ms} n {held} (es : Entries) (bs : Bodies) (ts : Mem) (vs : Votes)
             → StoreInv ms held
             → Wf storeG ms (blockStoreL n held ⦀ (ebStore n es ⦀ (bodyStore n bs ⦀
                               (mempool n ts ⦀ voteStore n vs))))
  wf-storesL n es bs ts vs inv =
    wf-⦀ (wf-blockStoreL n inv)
      (wf-⦀ (wf-ebStore n es)
      (wf-⦀ (wf-bodyStore n bs)
      (wf-⦀ (wf-mempool n ts) (wf-voteStore n vs))))

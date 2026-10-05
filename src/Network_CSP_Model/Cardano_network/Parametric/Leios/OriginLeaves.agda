{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE DISCIPLINE-INDEPENDENT LEAVES of an origin
-- safety proof over the assume-guarantee framework.
--
-- Every one of the Linear-Leios safety theorems (S1, S2, S2′, S3) gates ONE
-- node-local `store` channel and proves the gate by instantiating
-- `Parametric.BlockProvenance.Carrier` (and its returning-tree layer
-- `Parametric.BlockProvenanceWfR.Body`).  Most of that proof does not depend
-- on WHICH channel is gated, only on the fact that the gated channel is a
-- `store` channel.  This module is that part, written once.
--
-- ============ WHAT A CONSUMER MUST SUPPLY, PER INSTANCE ============
--
--   * the carrier data — `S`, `B`, `Carries`, `WA`, `next`, `_≤_` and its two
--     laws — i.e. exactly `BlockProvenance.Carrier`'s telescope.  A consumer
--     MUST open `BP.Carrier` and `BPW.Body` at the SAME arguments, so that
--     its `Wf`/`WfR` and this module's are the same record;
--   * `carries-store`: only a `store` channel carries anything.  That is the
--     one alphabet enumeration of the whole development (one clause per
--     `Net_Api` constructor, and under `store` one per `StoreTag`), and every
--     instance has to write it anyway to state its own gate.  Here it is
--     WEAKENED to "some store tag", which is what the peer bundle needs and
--     what makes this module reusable;
--   * the CONTENT-BEARING leaves, and the leaves whose channels the instance
--     gates.  See the exclusion below.
--
-- ============ WHAT IS FREE ============
--
--   * `wf-free` / `wfR-free` / `wf-∅` — the vacuous leaf at both carriers, and
--     the empty guarantee alphabet;
--   * `sep-store` / `sep-api` — both `Sep` side conditions of a node.  The
--     store one is vacuous BECAUSE the gated channel is a `store` channel,
--     hence inside `storeES`: that is the whole reason the stores of
--     `nodeLogicL` — `voteStore` included, which offers its deposit channel
--     for EVERY value — need no waiver and cost three lines;
--   * (`NoRet-ParR`, the right-sided mirror a node needs because it puts its
--     TERMINATING peer bundle on the LEFT, is NOT re-proved here: it already
--     exists as `BlockProvenanceSafe.Generic.NoRet-ParR`, at this very
--     telescope.  A consumer opens it from there.)
--   * THE WHOLE PEER BUNDLE.  Every peer is a `renameMap` of a mini-protocol
--     process and no mini-protocol event has a `store` channel in its image,
--     so `OffersOnly-renameMap-image` refutes the gate for ALL of them from
--     `carries-store` alone — six two-line facts, then `wf-slotP`,
--     `wf-nodeBundleP` and `wf-linkBundlesP`.  This is the fiddliest part of an
--     instance and it is now paid once.  Only the PROTOTYPE bundle (`…P`,
--     `PeersP.nodeBundleP`, hoisted out of `VoteSound` in Task 7) is here: the
--     nine `…R` facts of the old REPORTING bundle (`PeersR.nodeBundleR`) were
--     deleted in Task 8 once `CertSound`'s re-keying left them with no
--     consumer at all (`PeersRSanity` imports `PeersR`, not this module).
--
-- ============ WHAT IS *NOT* HERE, AND WHY ============
--
-- THE TWELVE THREAD WITNESSES ARE NOT DISCIPLINE-INDEPENDENT and stay with
-- their instance.  A thread is vacuous only if the channels it fires are not
-- the gated one, and which those are changes with the theorem: `NodeLogicL`'s
-- `forgeL` and `fetchBody` deposit an EB BODY, so they are vacuous for S2
-- (gated: `stPutVote`) and content-bearing for S1 (gated: `stPutBody`).
-- Parameterising them would take one `noNeed` premise per `StoreTag`, which is
-- longer than the witnesses themselves — and a premise an instance whose gated
-- tag is that one cannot supply at all.  They are cheap where they belong
-- (2–6 non-comment lines each) and they are written against a `Carries` that
-- REDUCES at a concrete channel, which a parameter never does.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.OriginLeaves where

open import Level using (Level; 0ℓ)
open import Data.Bool using (if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import Cardano_network.Params using (Params)
-- (wholesale, as `NetworkPar` and `BlockProvenancePeers`: `Dir`, its decidable
-- equality — which the peer bundle dispatches on — and the six `IDs` constructors)
open import Cardano_network.Base
open import Cardano_network.Parametric.Topology using (Topology; opposite)
import Cardano_network.Net as N
import Cardano_network.Data as D
import CSP.Operators as O
import Semantics.LTS as LTS
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.BlockProvenance as BP
import Cardano_network.Parametric.BlockProvenanceWfR as BPW
import CSP.Laws.Bisim.RenameOffers as RO

-- the shared leaves, parametric in the network parameters, the topology, the api
-- alphabet, `BlockProvenance.Carrier`'s whole telescope, and the ONE fact that ties
-- the gate to a `store` channel
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (S B : Set)
  (Carries : (at : AnyTypes (N.Net_Api p (D.Payload p))) → proj₁ at → B → Set)
  (WA      : S → B → Set)
  (next    : LTS.Label {E = N.Net_Api p (D.Payload p)}
                       {I = ExtI (N.Net_Api p (D.Payload p))} (⊤ {0ℓ}) → S → S)
  (_≤_     : S → S → Set)
  (≤-refl  : ∀ {s} → s ≤ s)
  (≤-trans : ∀ {s₁ s₂ s₃} → s₁ ≤ s₂ → s₂ ≤ s₃ → s₁ ≤ s₃)
  (next-≤  : ∀ a s → s ≤ next a s)
  where

  open Params p using (linkConfig)
  open N p
    using (Link; Net_Api; Net_Api-≟; StoreTag; StoreCar; store)
  open D p using (Payload)
  open Topology t using (Node; endpointsOf)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (EventSet; Skip)
  open import Cardano_network.Parametric.Node p t apiES
    using (Proc; bundleAtWith; linkBundlesWith)
  open import Cardano_network.KeepAlive    p using (KAEv; KAEv-≟)
  open import Cardano_network.ChainSync    p using (CSEv; CSEv-≟)
  open import Cardano_network.BlockFetch   p using (BFEv; BFEv-≟)
  open import Cardano_network.TxSubmission p using (TSEv; TSEv-≟)
  open import Cardano_network.NetworkPar p
    using ( ιKA; ιKA⁻¹; ιKA-linv; ιBF; ιBF⁻¹; ιBF-linv; ιCS; ιCS⁻¹; ιCS-linv
          ; ιTS; ιTS⁻¹; ιTS-linv )
  -- the two PROTOTYPE mini-protocols and the prototype peer bundle, for the `…P`
  -- siblings at the bottom of `Leaves` (hoisted out of `VoteSound` in Task 7)
  open import Cardano_network.LeiosNotifyP p using (LNPEv; LNPEv-≟)
  open import Cardano_network.LeiosFetchP  p using (LFPEv; LFPEv-≟)
  open import Cardano_network.Parametric.Leios.PeersP p
    using ( ιLNP; ιLNP⁻¹; ιLNP-linv; ιLFP; ιLFP⁻¹; ιLFP-linv
          ; clientPeerP; serverPeerP; nodeBundleP )
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using (Alpha; OffersOnly)
  open NL.Generic p t apiES using (storeES)

  -- the assume-guarantee carrier at the consumer's own data …
  open BP.Carrier (Net_Api-≟ {Payload}) S B Carries WA next _≤_ ≤-trans next-≤
    using (Wf; nowW; stepW; wf-Skip; Sep; wf-⦀; wf-⦀⋆)

  -- … and its returning-tree layer, at the SAME arguments, so the two `Wf`s — and the
  -- consumer's, opened at those same arguments — are one record
  open BPW.Body (Net_Api-≟ {Payload}) S B Carries WA next _≤_ ≤-refl ≤-trans next-≤
    using (WfR; nowR; stepR; retR; wf-⦀⁺)

  ------------------------------------------------------------------------
  -- THE LEAVES, under the one fact that ties the gate to a `store` channel
  --
  -- A SEPARATE INNER MODULE because the fact's type mentions `store` and `StoreTag`,
  -- which are only in scope after `open N p` above — a module telescope cannot name
  -- them, and writing them qualified does not elaborate (`N.store p l d m` reads `p`
  -- as the link).
  ------------------------------------------------------------------------

  -- ONLY A `store` CHANNEL CARRIES ANYTHING.  Each instance proves this by the one
  -- alphabet enumeration it has to write anyway to state its own gate; here only the
  -- `store` head matters, which is what makes this module serve all four theorems.
  module Leaves
    (carries-store : ∀ {X} {e : Net_Api Payload X} {a : X} {b} → Carries (X , e) a b
                   → Σ[ l ∈ Link ] Σ[ d ∈ Dir ] Σ[ m ∈ StoreTag ]
                       (_≡_ {A = AnyTypes (Net_Api Payload)}
                            (X , e) (StoreCar m , store l d m)))
    where

  ------------------------------------------------------------------------
  -- The two guarantee alphabets, and the vacuous leaf
  ------------------------------------------------------------------------

    -- THE FULL ALPHABET: a component that guarantees the gate on every label it performs
    fullα : Alpha
    fullα _ _ = ⊤

    -- THE EMPTY ALPHABET: a component that guarantees nothing.  This is the STORE side
    -- of a node: the store offers its deposit channel for EVERY value, so it cannot
    -- carry the gate — and it does not have to, because the gated channel is a `store`
    -- channel, hence inside `storeES`, and `Sep` therefore never asks it.
    ∅α : Alpha
    ∅α _ _ = ⊥

    -- a component guaranteeing nothing is well-formed outright
    wf-∅ : ∀ {ms} {M : Proc} → Wf ∅α ms M
    wf-∅ .nowW  _ ()
    wf-∅ .stepW _ st _ = wf-∅

    -- an alphabet whose events carry nothing: the confinement every leaf but the
    -- instance's content-bearing ones satisfies
    noNeed : Alpha
    noNeed at a = ∀ {b} → Carries at a b → ⊥

    -- A LEAF THAT CARRIES NOTHING is well-formed on EVERY guarantee alphabet at every
    -- state: its `OK` obligation has no witness to discharge.  `OffersOnly` is the
    -- repo's own step-closed confinement invariant, with closure lemmas for every
    -- operator the threads are built from.
    wf-free : ∀ {G ms} {M : Proc} → OffersOnly noNeed M → Wf G ms M
    wf-free oo .nowW  _ _ st = λ c → ⊥-elim (OffersOnly.now oo st c)
    wf-free oo .stepW _ st _ = wf-free (OffersOnly.step oo st)

    -- … and the same at the returning-tree carrier, for a body used inside a loop
    wfR-free : ∀ {ℓr} {R : Set ℓr} {G ms} {Inv : S → R → Set}
                 {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
             → OffersOnly noNeed M → (∀ {ms′ r} → Inv ms′ r) → WfR G ms Inv M
    wfR-free oo inv .nowR  _ _ st = λ c → ⊥-elim (OffersOnly.now oo st c)
    wfR-free oo inv .stepR _ st _ = wfR-free (OffersOnly.step oo st) inv
    wfR-free oo inv .retR  _ _    = inv

    ------------------------------------------------------------------------
    -- The two `Sep` side conditions of a node
    ------------------------------------------------------------------------

    -- SEP AT THE STORE RENDEZVOUS: the only carrying channels are `store` channels, and
    -- every `store` channel is in `storeES` — so both halves are vacuous
    sep-store : Sep storeES fullα ∅α
    sep-store = (λ c _ ¬m → ⊥-elim (¬m (mem-store c))) , (λ _ ())
      where
      -- a carrying channel is a store channel, and every store channel is in `storeES`
      mem-store : ∀ {X} {e : Net_Api Payload X} {a : X} {b} → Carries (X , e) a b
                → EventSet.mem storeES (X , e) a
      mem-store c with carries-store c
      ... | _ , _ , _ , refl = tt

    -- SEP AT THE API RENDEZVOUS: both operands carry the full alphabet, so nothing to do
    sep-api : Sep apiES fullα fullα
    sep-api = (λ _ _ _ → tt) , (λ _ _ _ → tt)

    ------------------------------------------------------------------------
    -- The four stock mini-protocol renamings
    --
    -- Every peer is a `renameMap` of a mini-protocol process, and no mini-protocol
    -- event has a `store` channel in its image, so no peer can ever fire the gated
    -- label.  `OffersOnly-renameMap-image` reads that off the renaming alone, whatever
    -- the peer does — which is what makes a bundle that TERMINATES on `done` harmless
    -- here: `Wf` carries no `noTick` obligation.
    ------------------------------------------------------------------------

    -- one `RenameOffers` instance per stock protocol renaming, for the image lemmas below
    module RKA = RO KAEv-≟ (Net_Api-≟ {Payload}) ιKA ιKA⁻¹ ιKA-linv
    module RBF = RO BFEv-≟ (Net_Api-≟ {Payload}) ιBF ιBF⁻¹ ιBF-linv
    module RCS = RO CSEv-≟ (Net_Api-≟ {Payload}) ιCS ιCS⁻¹ ιCS-linv
    module RTS = RO TSEv-≟ (Net_Api-≟ {Payload}) ιTS ιTS⁻¹ ιTS-linv

    -- any KeepAlive-renamed peer carries nothing
    ooKA : ∀ {ℓr} {R : Set ℓr} {P : PTree KAEv (ExtI KAEv) R} → OffersOnly noNeed (RKA.renameMap P)
    ooKA = RKA.OffersOnly-renameMap-image
             (λ bt b at a eq c → case carries-store c of λ { (_ , _ , _ , refl) → case eq of λ () })

    -- any BlockFetch-renamed peer carries nothing
    ooBF : ∀ {ℓr} {R : Set ℓr} {P : PTree BFEv (ExtI BFEv) R} → OffersOnly noNeed (RBF.renameMap P)
    ooBF = RBF.OffersOnly-renameMap-image
             (λ bt b at a eq c → case carries-store c of λ { (_ , _ , _ , refl) → case eq of λ () })

    -- any ChainSync-renamed peer carries nothing
    ooCS : ∀ {ℓr} {R : Set ℓr} {P : PTree CSEv (ExtI CSEv) R} → OffersOnly noNeed (RCS.renameMap P)
    ooCS = RCS.OffersOnly-renameMap-image
             (λ bt b at a eq c → case carries-store c of λ { (_ , _ , _ , refl) → case eq of λ () })

    -- any TxSubmission-renamed peer carries nothing
    ooTS : ∀ {ℓr} {R : Set ℓr} {P : PTree TSEv (ExtI TSEv) R} → OffersOnly noNeed (RTS.renameMap P)
    ooTS = RTS.OffersOnly-renameMap-image
             (λ bt b at a eq c → case carries-store c of λ { (_ , _ , _ , refl) → case eq of λ () })

    ------------------------------------------------------------------------
    -- The PROTOTYPE peer bundle
    --
    -- The nine facts for `PeersP.nodeBundleP`.  They were written inside
    -- `VoteSound.Generic` by Task 6 and hoisted here by Task 7, when S3 became the
    -- second prototype instance to need them.  Their nine `…R` siblings, for the old
    -- REPORTING bundle `PeersR.nodeBundleR`, were DELETED in Task 8: S3's re-keying was
    -- the last consumer, and `PeersRSanity` imports `PeersR` directly, not this module.
    -- Every prototype peer is a `renameMap` of a mini-protocol process and no
    -- mini-protocol event has a `store` channel in its image, so `carries-store` alone
    -- refutes the gate for all of them.
    ------------------------------------------------------------------------

    -- the `RenameOffers` instance of the prototype LeiosNotify renaming
    module RLNP = RO LNPEv-≟ (Net_Api-≟ {Payload}) ιLNP ιLNP⁻¹ ιLNP-linv

    -- the `RenameOffers` instance of the prototype LeiosFetch renaming
    module RLFP = RO LFPEv-≟ (Net_Api-≟ {Payload}) ιLFP ιLFP⁻¹ ιLFP-linv

    -- any prototype-LeiosNotify-renamed peer carries nothing
    ooLNP : ∀ {ℓr} {R : Set ℓr} {P : PTree LNPEv (ExtI LNPEv) R}
          → OffersOnly noNeed (RLNP.renameMap P)
    ooLNP = RLNP.OffersOnly-renameMap-image
              (λ bt b at a eq c → case carries-store c of λ { (_ , _ , _ , refl) → case eq of λ () })

    -- any prototype-LeiosFetch-renamed peer carries nothing
    ooLFP : ∀ {ℓr} {R : Set ℓr} {P : PTree LFPEv (ExtI LFPEv) R}
          → OffersOnly noNeed (RLFP.renameMap P)
    ooLFP = RLFP.OffersOnly-renameMap-image
              (λ bt b at a eq c → case carries-store c of λ { (_ , _ , _ , refl) → case eq of λ () })

    -- a PROTOTYPE client peer of any configured instance
    wf-clientPeerP : ∀ {ms} l d id → Wf fullα ms (clientPeerP l d id)
    wf-clientPeerP l d N2N_KeepAlive    = wf-free ooKA
    wf-clientPeerP l d N2N_ChainSync    = wf-free ooCS
    wf-clientPeerP l d N2N_BlockFetch   = wf-free ooBF
    wf-clientPeerP l d N2N_TxSubmission = wf-free ooTS
    wf-clientPeerP l d N2N_LeiosNotify  = wf-free ooLNP
    wf-clientPeerP l d N2N_LeiosFetch   = wf-free ooLFP

    -- … and a PROTOTYPE server peer (the two prototype producers, the reply-reporting
    -- TxSubmission requester `PeersR.TSserverRA`, and the stock producers elsewhere)
    wf-serverPeerP : ∀ {ms} l d id → Wf fullα ms (serverPeerP l d id)
    wf-serverPeerP l d N2N_KeepAlive    = wf-free ooKA
    wf-serverPeerP l d N2N_ChainSync    = wf-free ooCS
    wf-serverPeerP l d N2N_BlockFetch   = wf-free ooBF
    wf-serverPeerP l d N2N_TxSubmission = wf-free ooTS
    wf-serverPeerP l d N2N_LeiosNotify  = wf-free ooLNP
    wf-serverPeerP l d N2N_LeiosFetch   = wf-free ooLFP

    -- one configured instance's slot in `nodeBundleP`: client on `cl`, prototype server
    -- on `sv`, `Skip` otherwise (the `with` mirrors the bundle's own dispatch)
    wf-slotP : ∀ {ms} (l : Link) (cl sv d : Dir) (id : IDs)
             → Wf fullα ms (if ⌊ d ≟ cl ⌋ then clientPeerP l d id
                            else if ⌊ d ≟ sv ⌋ then serverPeerP l d id else Skip)
    wf-slotP l cl sv d id with d ≟ cl
    ... | yes _ = wf-clientPeerP l d id
    ... | no _ with d ≟ sv
    ...   | yes _ = wf-serverPeerP l d id
    ...   | no _  = wf-Skip

    -- THE PROTOTYPE PEER BUNDLE of one node on one link
    wf-nodeBundleP : ∀ {ms} (l : Link) (cl sv : Dir) → Wf fullα ms (nodeBundleP l cl sv)
    wf-nodeBundleP l cl sv = wf-⦀⋆ _ (linkConfig l) (λ { (d , id) → wf-slotP l cl sv d id })

    -- EVERY INCIDENT ENDPOINT'S PROTOTYPE BUNDLE, interleaved: the left operand of a node
    wf-linkBundlesP : ∀ {ms} n → Wf fullα ms (linkBundlesWith nodeBundleP n)
    wf-linkBundlesP n =
      wf-⦀⁺ (bundleAtWith nodeBundleP) (proj₁ (endpointsOf n)) (proj₂ (endpointsOf n))
            (λ ld → wf-nodeBundleP (proj₁ ld) (proj₂ ld) (opposite (proj₂ ld)))

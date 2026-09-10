{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — BLOCK PROVENANCE AT THE PEER BUNDLE: every
-- configured mini-protocol peer, and hence `NetworkPar.nodeBundle`, is
-- well-formed (`BlockProvenance.Wf`) on the peers' alphabet `peersG`.
--
-- Two kinds of peer, two arguments:
--
--   * THE BLOCKFETCH PEERS relay blocks.  Their facts are proved at the
--     source alphabet in `Parametric.BlockProvenanceBF` and TRANSPORTED
--     here along `ιBF` by `BlockProvenance.Rename.wf-renameMap`.  Because
--     the source alphabet/carrier there are PULLBACKS of `peersG`/`Carries`
--     along `ιBF`, the three transport premises are three `subst`s of ONE
--     fact — `vis-inv-sound`: `ι-vis-inv bt b ≡ just (at , a)` forces
--     `(bt , b) ≡ ((_ , ιBF (proj₂ at)) , a)` — which is in turn the
--     33-clause observation that `ιBF⁻¹` answers `just` only on the image
--     of `ιBF`.
--
--   * EVERY OTHER PEER is vacuous, by `Carrier.Vacuous`: a `renameMap`
--     only performs image labels, and for KA/CS/TS/LF no image label
--     carries a block at all; for LN the only one that does is the
--     announcement, which is the LN SERVER PEER'S RELY and so is outside
--     `peersG` (the announcement is `apiES`-synchronised and pinned by
--     `lnServerLoop` — the same handedness `AnnounceSafeLeaves.safe-ParE`
--     found).  Each costs one seven-clause case split on `Carries`.
--
-- `nodeBundle` is `⦀⋆` over the configured instances of one link, each
-- slot a `Dir`-dispatch between client peer, server peer and `Skip`; the
-- bundle fact is `wf-⦀⋆` over `wf-slot`.
--
-- FOR TASK 5.  `peersG` excludes `output _ _ _` (the client peer's rely
-- from the medium).  `wf-Par`'s `Sep apiES` demands that the node-logic
-- alphabet agree with `peersG` on every block-carrying label OUTSIDE
-- `apiES`, and `output` is such a label — so `BlockProvenanceNode.nodeG`
-- must be shrunk to exclude `output` too before the two halves compose
-- (`wf-mono-G`, free: the node logic never performs `output`).  The
-- union is then "everything but `output`", which is what the medium's
-- half must supply at the top level.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.BlockProvenancePeers where

open import Level using (0ℓ)
open import Data.Bool using (if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
import Data.Unit.Polymorphic as Poly
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Class.DecEq using (_≟_)

open import Process_Trees using (AnyTypes)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceBF as BPBF

-- the same three parameters as every other `Parametric.BlockProvenance*` module
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (Block; linkConfig)
  -- (wholesale, as `NetworkPar`: the `Dir` decidable equality the bundle dispatches on)
  open import CSP.Examples.Cardano_network.Base
  open N p
    using ( Link; Net_Api; Net_Api-≟
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; store; env; break
          ; recvBFBlock )
  open D p using (Payload)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (Skip)
  open import CSP.Examples.Cardano_network.BlockFetch p
    using (BFEv; sendBF; receiveBF; apiBFev; doneBF; BFEv-≟)
  open import CSP.Examples.Cardano_network.NetworkPar p
    using ( ιKA; ιKA⁻¹; ιKA-linv; ιBF; ιBF⁻¹; ιBF-linv; ιCS; ιCS⁻¹; ιCS-linv
          ; ιTS; ιTS⁻¹; ιTS-linv; ιLN; ιLN⁻¹; ιLN-linv; ιLF; ιLF⁻¹; ιLF-linv
          ; BFclientA; BFserverA; clientPeer; serverPeer; nodeBundle )
  import CSP.Rename {E₁ = BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RenBF
  open AS.Generic p t apiES using (Minted)
  open AI.Generic p t apiES using (WellAnnounced)
  open BP.Generic p t apiES
  open BPBF.Generic p t apiES using (peersG; bfG; CarriesBF; wf-BFclient; wf-BFserver)

  ------------------------------------------------------------------------
  -- The BlockFetch peers: transport along `ιBF`
  ------------------------------------------------------------------------

  -- the two carriers the transport relates: the state-agnostic source one of
  -- `BlockProvenanceBF` and this module's target one — the SAME arguments both give
  module RBF = BP.Rename BFEv-≟ (Net_Api-≟ {Payload}) ιBF ιBF⁻¹ ιBF-linv
                         Minted Block CarriesBF Carries WellAnnounced
                         next _⊆_ ⊆-refl ⊆-trans next-⊇

  -- `ιBF⁻¹` answers `just e₁` only on `ιBF e₁`: one clause per `Net_Api` shape, the
  -- wire channels split on their protocol id
  ιBF⁻¹-sound : ∀ {A} (e₂ : Net_Api Payload A) (e₁ : BFEv A)
              → ιBF⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιBF e₁
  ιBF⁻¹-sound (input  _ _ N2N_BlockFetch)   _ refl = refl
  ιBF⁻¹-sound (input  _ _ N2N_ChainSync)    _ ()
  ιBF⁻¹-sound (input  _ _ N2N_TxSubmission) _ ()
  ιBF⁻¹-sound (input  _ _ N2N_KeepAlive)    _ ()
  ιBF⁻¹-sound (input  _ _ N2N_LeiosNotify)  _ ()
  ιBF⁻¹-sound (input  _ _ N2N_LeiosFetch)   _ ()
  ιBF⁻¹-sound (output _ _ N2N_BlockFetch)   _ refl = refl
  ιBF⁻¹-sound (output _ _ N2N_ChainSync)    _ ()
  ιBF⁻¹-sound (output _ _ N2N_TxSubmission) _ ()
  ιBF⁻¹-sound (output _ _ N2N_KeepAlive)    _ ()
  ιBF⁻¹-sound (output _ _ N2N_LeiosNotify)  _ ()
  ιBF⁻¹-sound (output _ _ N2N_LeiosFetch)   _ ()
  ιBF⁻¹-sound (done   _ _ N2N_BlockFetch)   _ refl = refl
  ιBF⁻¹-sound (done   _ _ N2N_ChainSync)    _ ()
  ιBF⁻¹-sound (done   _ _ N2N_TxSubmission) _ ()
  ιBF⁻¹-sound (done   _ _ N2N_KeepAlive)    _ ()
  ιBF⁻¹-sound (done   _ _ N2N_LeiosNotify)  _ ()
  ιBF⁻¹-sound (done   _ _ N2N_LeiosFetch)   _ ()
  ιBF⁻¹-sound (apiBF  _ _ _) _ refl = refl
  ιBF⁻¹-sound (sndmsg _ _ _) _ ()
  ιBF⁻¹-sound (rcvmsg _ _ _) _ ()
  ιBF⁻¹-sound (tx     _ _ _) _ ()
  ιBF⁻¹-sound (sndack _ _ _) _ ()
  ιBF⁻¹-sound (rcvack _ _ _) _ ()
  ιBF⁻¹-sound (ack    _ _ _) _ ()
  ιBF⁻¹-sound (apiCS  _ _ _) _ ()
  ιBF⁻¹-sound (apiTS  _ _ _) _ ()
  ιBF⁻¹-sound (apiKA  _ _ _) _ ()
  ιBF⁻¹-sound (apiLN  _ _ _) _ ()
  ιBF⁻¹-sound (apiLF  _ _ _) _ ()
  ιBF⁻¹-sound (store  _ _ _) _ ()
  ιBF⁻¹-sound (env    _ _ _) _ ()
  ιBF⁻¹-sound (break  _)     _ ()

  -- a concrete target event: a channel and a value on it
  ConcEv : Set₁
  ConcEv = Σ[ bt ∈ AnyTypes (Net_Api Payload) ] proj₁ bt

  -- THE ONE TRANSPORT FACT: `ι-vis-inv` answers `just (at , a)` only on the ι-image
  -- of `at`, carrying that same `a`
  vis-inv-sound : ∀ bt b at a → RenBF.ι-vis-inv bt b ≡ just (at , a)
                → _≡_ {A = ConcEv} (bt , b) ((proj₁ at , ιBF (proj₂ at)) , a)
  vis-inv-sound (A , e₂) b at a eq with ιBF⁻¹ e₂ in eq′
  ... | nothing = case eq of λ ()
  ... | just e₁ with just-injective eq
  ...   | refl = cong (λ e → (A , e) , b) (ιBF⁻¹-sound e₂ e₁ eq′)

  -- the three premises of `wf-renameMap`, each a `subst` along it: the alphabet pulls
  -- back, and the carried block is the same on both sides
  al : ∀ bt b at a → RenBF.ι-vis-inv bt b ≡ just (at , a) → peersG bt b → bfG at a
  al bt b (A , e) a eq = subst (λ ce → peersG (proj₁ ce) (proj₂ ce)) (vis-inv-sound bt b (A , e) a eq)

  c→ : ∀ bt b at a → RenBF.ι-vis-inv bt b ≡ just (at , a)
     → ∀ {blk} → Carries bt b blk → CarriesBF at a blk
  c→ bt b (A , e) a eq {blk} =
    subst (λ ce → Carries (proj₁ ce) (proj₂ ce) blk) (vis-inv-sound bt b (A , e) a eq)

  c← : ∀ bt b at a → RenBF.ι-vis-inv bt b ≡ just (at , a)
     → ∀ {blk} → CarriesBF at a blk → Carries bt b blk
  c← bt b (A , e) a eq {blk} =
    subst (λ ce → Carries (proj₁ ce) (proj₂ ce) blk) (sym (vis-inv-sound bt b (A , e) a eq))

  -- THE BLOCKFETCH PEERS, in the network alphabet
  wf-BFclientA : ∀ {ms} (l : Link) (d : Dir) → Wf peersG ms (BFclientA l d)
  wf-BFclientA l d = RBF.wf-renameMap al c→ c← (wf-BFclient l d)

  wf-BFserverA : ∀ {ms} (l : Link) (d : Dir) → Wf peersG ms (BFserverA l d)
  wf-BFserverA l d = RBF.wf-renameMap al c→ c← (wf-BFserver l d)

  ------------------------------------------------------------------------
  -- The other peers: vacuous
  ------------------------------------------------------------------------

  module VKA = Vacuous ιKA ιKA⁻¹ ιKA-linv
  module VCS = Vacuous ιCS ιCS⁻¹ ιCS-linv
  module VTS = Vacuous ιTS ιTS⁻¹ ιTS-linv
  module VLN = Vacuous ιLN ιLN⁻¹ ιLN-linv
  module VLF = Vacuous ιLF ιLF⁻¹ ιLF-linv

  -- no block-carrying channel is in the image of the KeepAlive renaming: on each of
  -- the seven `Carries` shapes `ιKA⁻¹` answers `nothing`
  hKA : ∀ bt b at a → VKA.ι-vis-inv bt b ≡ just (at , a) → peersG bt b
      → ∀ {blk} → ¬ Carries bt b blk
  hKA _ _ _ _ eq _ c-stGet  = case eq of λ ()
  hKA _ _ _ _ eq _ c-stPut  = case eq of λ ()
  hKA _ _ _ _ eq _ c-sendBF = case eq of λ ()
  hKA _ _ _ _ eq _ c-recvBF = case eq of λ ()
  hKA _ _ _ _ eq _ c-ann    = case eq of λ ()
  hKA _ _ _ _ eq _ c-input  = case eq of λ ()
  hKA _ _ _ _ eq _ c-output = case eq of λ ()

  -- likewise ChainSync
  hCS : ∀ bt b at a → VCS.ι-vis-inv bt b ≡ just (at , a) → peersG bt b
      → ∀ {blk} → ¬ Carries bt b blk
  hCS _ _ _ _ eq _ c-stGet  = case eq of λ ()
  hCS _ _ _ _ eq _ c-stPut  = case eq of λ ()
  hCS _ _ _ _ eq _ c-sendBF = case eq of λ ()
  hCS _ _ _ _ eq _ c-recvBF = case eq of λ ()
  hCS _ _ _ _ eq _ c-ann    = case eq of λ ()
  hCS _ _ _ _ eq _ c-input  = case eq of λ ()
  hCS _ _ _ _ eq _ c-output = case eq of λ ()

  -- likewise TxSubmission
  hTS : ∀ bt b at a → VTS.ι-vis-inv bt b ≡ just (at , a) → peersG bt b
      → ∀ {blk} → ¬ Carries bt b blk
  hTS _ _ _ _ eq _ c-stGet  = case eq of λ ()
  hTS _ _ _ _ eq _ c-stPut  = case eq of λ ()
  hTS _ _ _ _ eq _ c-sendBF = case eq of λ ()
  hTS _ _ _ _ eq _ c-recvBF = case eq of λ ()
  hTS _ _ _ _ eq _ c-ann    = case eq of λ ()
  hTS _ _ _ _ eq _ c-input  = case eq of λ ()
  hTS _ _ _ _ eq _ c-output = case eq of λ ()

  -- LeiosNotify: the ONE block-carrying channel in its image is the announcement,
  -- and that is outside `peersG` — the LN server peer RELIES on it
  hLN : ∀ bt b at a → VLN.ι-vis-inv bt b ≡ just (at , a) → peersG bt b
      → ∀ {blk} → ¬ Carries bt b blk
  hLN _ _ _ _ eq _ c-stGet  = case eq of λ ()
  hLN _ _ _ _ eq _ c-stPut  = case eq of λ ()
  hLN _ _ _ _ eq _ c-sendBF = case eq of λ ()
  hLN _ _ _ _ eq _ c-recvBF = case eq of λ ()
  hLN _ _ _ _ _  g c-ann    = g
  hLN _ _ _ _ eq _ c-input  = case eq of λ ()
  hLN _ _ _ _ eq _ c-output = case eq of λ ()

  -- likewise LeiosFetch
  hLF : ∀ bt b at a → VLF.ι-vis-inv bt b ≡ just (at , a) → peersG bt b
      → ∀ {blk} → ¬ Carries bt b blk
  hLF _ _ _ _ eq _ c-stGet  = case eq of λ ()
  hLF _ _ _ _ eq _ c-stPut  = case eq of λ ()
  hLF _ _ _ _ eq _ c-sendBF = case eq of λ ()
  hLF _ _ _ _ eq _ c-recvBF = case eq of λ ()
  hLF _ _ _ _ eq _ c-ann    = case eq of λ ()
  hLF _ _ _ _ eq _ c-input  = case eq of λ ()
  hLF _ _ _ _ eq _ c-output = case eq of λ ()

  ------------------------------------------------------------------------
  -- The bundle
  ------------------------------------------------------------------------

  -- the client peer of each protocol, on `peersG`
  wf-clientPeer : ∀ {ms} (l : Link) (d : Dir) (id : IDs) → Wf peersG ms (clientPeer l d id)
  wf-clientPeer l d N2N_KeepAlive    = VKA.wf-renameMap-vacuous hKA
  wf-clientPeer l d N2N_ChainSync    = VCS.wf-renameMap-vacuous hCS
  wf-clientPeer l d N2N_BlockFetch   = wf-BFclientA l d
  wf-clientPeer l d N2N_TxSubmission = VTS.wf-renameMap-vacuous hTS
  wf-clientPeer l d N2N_LeiosNotify  = VLN.wf-renameMap-vacuous hLN
  wf-clientPeer l d N2N_LeiosFetch   = VLF.wf-renameMap-vacuous hLF

  -- and the server peer
  wf-serverPeer : ∀ {ms} (l : Link) (d : Dir) (id : IDs) → Wf peersG ms (serverPeer l d id)
  wf-serverPeer l d N2N_KeepAlive    = VKA.wf-renameMap-vacuous hKA
  wf-serverPeer l d N2N_ChainSync    = VCS.wf-renameMap-vacuous hCS
  wf-serverPeer l d N2N_BlockFetch   = wf-BFserverA l d
  wf-serverPeer l d N2N_TxSubmission = VTS.wf-renameMap-vacuous hTS
  wf-serverPeer l d N2N_LeiosNotify  = VLN.wf-renameMap-vacuous hLN
  wf-serverPeer l d N2N_LeiosFetch   = VLF.wf-renameMap-vacuous hLF

  -- one configured instance's slot in `nodeBundle`: client on `cl`, server on `sv`,
  -- `Skip` otherwise (the `with` mirrors the bundle's own dispatch)
  wf-slot : ∀ {ms} (l : Link) (cl sv d : Dir) (id : IDs)
          → Wf peersG ms (if ⌊ d ≟ cl ⌋ then clientPeer l d id
                          else if ⌊ d ≟ sv ⌋ then serverPeer l d id else Skip)
  wf-slot l cl sv d id with d ≟ cl
  ... | yes _ = wf-clientPeer l d id
  ... | no _ with d ≟ sv
  ...   | yes _ = wf-serverPeer l d id
  ...   | no _  = wf-Skip

  -- THE PEER BUNDLE of one node on one link, over exactly the configured instances
  wf-nodeBundle : ∀ {ms} (l : Link) (cl sv : Dir) → Wf peersG ms (nodeBundle l cl sv)
  wf-nodeBundle l cl sv = wf-⦀⋆ _ (linkConfig l) (λ { (d , id) → wf-slot l cl sv d id })

  ------------------------------------------------------------------------
  -- Non-vacuity: the peers' guarantees are real guarantees
  ------------------------------------------------------------------------

  -- the two block-carrying channels the BlockFetch peers EMIT on are in `peersG`, so
  -- `nowW` of the facts above really says "the delivered/forwarded block is
  -- well-announced" (the announce channel is deliberately NOT here — it is a rely
  -- at this level; `AnnIn` is met by `BlockProvenanceNode.threadsG`)
  peersG-recvBF : ∀ {l d} (b : Block) → peersG (_ , apiBF l d recvBFBlock) b
  peersG-recvBF _ = Poly.tt

  peersG-input : ∀ {l d} (x : Payload) → peersG (_ , input l d N2N_BlockFetch) x
  peersG-input _ = Poly.tt

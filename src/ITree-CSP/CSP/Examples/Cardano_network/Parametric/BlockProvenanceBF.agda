{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — BLOCK PROVENANCE AT THE BLOCKFETCH PEERS,
-- proved over the peers' OWN alphabet `BFEv`.
--
-- The two BlockFetch peers are `renameMap`s along `ιBF : BFEv ↪ Net_Api`
-- of `iter`-loops over `BFEv` (`BlockFetch.clientStep`/`serverStep`).
-- Their `Wf` facts are proved HERE, at the source alphabet, and carried
-- across the renaming in `Parametric.BlockProvenancePeers`.  Both peers
-- are RELAYS with no register: `BFState` has four constructors and no
-- block field, so a block lives in exactly one continuation —
--
--   client, `stStreaming`: rely  `receiveBF l d ? (…, MsgBlock b)`
--                          guarantee `apiBFev l d recvBFBlock ! b`
--   server, `stStreaming`: rely  `apiBFev l d sendBFBlock ? b`
--                          guarantee `sendBF l d ! (…, MsgBlock b)`
--
-- and every other menu entry either carries no block or is answered
-- `nothing`.  One `with` per relay, both directions, as the plan said.
--
-- THE ALPHABET AND THE CARRIER ARE PULLBACKS.  `bfG`/`CarriesBF` are the
-- Cardano `peersG`/`Carries` read through `ιBF`, not a second enumeration.
-- So the three transport premises of `BlockProvenance.Rename.wf-renameMap`
-- reduce to ONE soundness fact about `ι-vis-inv` (next door), and the
-- proofs below pattern-match on the Cardano `Carries` constructors
-- directly (`c-output`, `c-recvBF`, …).
--
-- `peersG` is the ONE guarantee alphabet of a whole peer bundle (`wf-⦀`
-- interleaves on a single alphabet): every label except the bundle's
-- three relies — a block delivered by the medium (`output`), a block
-- handed to the BF server peer (`apiBF sendBFBlock`), and the header
-- handed to the LN server peer (`apiLN sendLNBlockAnnouncement`; the
-- announcement is pinned by `lnServerLoop`, so the peer must NOT
-- guarantee it).  Each rely is `apiES`- or `ioES`-synchronised.
--
-- This module is deliberately the `BFEv`-side half of a two-module split
-- (the Cardano-side transport is `BlockProvenancePeers`), as
-- `BlockProvenanceWfR`/`BlockProvenanceNode` are.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.BlockProvenanceBF where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Unit.Polymorphic as Poly
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Laws.Bisim.DRCongruenceRep as DR
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceWfR as BPW

-- the same three parameters as every other `Parametric.BlockProvenance*` module
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  -- the SAME opens as `BlockFetch`, so `_≟_` on links/directions and the `DecEq`
  -- instances inside the peers' `!`-outputs elaborate to the terms the peers were
  -- built with (the `with`s below have to abstract exactly those)
  open Params p
  open import CSP.Examples.Cardano_network.Base
  open import CSP.Examples.Cardano_network.Data p
  open import CSP.Examples.Cardano_network.Net p
  open import CSP.Examples.Cardano_network.BlockFetch p
    using ( BFEv; sendBF; receiveBF; apiBFev; doneBF; BFEv-≟; Rr
          ; BFState; stIdle; stBusy; stStreaming; stDone
          ; clientStep; serverStep; BFclientStClient; BFserverStClient )
  open import CSP.Examples.Cardano_network.NetworkPar p using (ιBF)
  open O {E = BFEv} BFEv-≟ using (iter)
  open import Semantics.LTS {E = BFEv} {I = ExtI BFEv}
    using (sRet; sSil; sVis; sTau)
  open AS.Generic p t apiES using (Minted)
  open AI.Generic p t apiES using (WellAnnounced; wellAnnounced-mono)
  open BP.Generic p t apiES using (Carries; c-sendBF; c-recvBF; c-input; c-output)

  ------------------------------------------------------------------------
  -- The alphabets and the source carrier
  ------------------------------------------------------------------------

  -- THE PEERS' GUARANTEE ALPHABET: everything but the bundle's three relies
  peersG : DR.Alpha (Net_Api-≟ {Payload})
  peersG (_ , output _ _ _)                       _ = ⊥
  peersG (_ , apiBF  _ _ sendBFBlock)             _ = ⊥
  peersG (_ , apiLN  _ _ sendLNBlockAnnouncement) _ = ⊥
  peersG _                                        _ = Poly.⊤

  -- its pullback along `ιBF`: the BlockFetch peers' alphabet at the source
  bfG : DR.Alpha BFEv-≟
  bfG (A , e) a = peersG (A , ιBF e) a

  -- the pullback of the Cardano `Carries`: which `BFEv` events carry which block
  CarriesBF : (at : AnyTypes BFEv) → proj₁ at → Block → Set
  CarriesBF (A , e) a b = Carries (A , ιBF e) a b

  -- the source carrier, STATE-AGNOSTIC (`next = λ _ s → s`): a peer never mints.
  -- These are exactly the arguments `BlockProvenance.Rename` gives its `C1`.
  open BP.Carrier BFEv-≟ Minted Block CarriesBF WellAnnounced
                  (λ _ s → s) _⊆_ ⊆-trans (λ _ _ → ⊆-refl)
    using (Wf)
  open BPW.Body BFEv-≟ Minted Block CarriesBF WellAnnounced
                (λ _ s → s) _⊆_ ⊆-refl ⊆-trans (λ _ _ → ⊆-refl)

  -- the loop invariant of an `iter`ed peer: none (the block never outlives a step)
  Inv⊤ : Minted → BFState ⊎ Rr → Set
  Inv⊤ = InvSum (λ _ _ → Poly.⊤)

  -- a peer `iter`s its step function from `stIdle`; `iter k q = iter-bind (k q) k`
  wf-peer : ∀ {ms} (k : BFState → PTree BFEv (ExtI BFEv) (BFState ⊎ Rr))
          → (∀ {ms′} q → WfR bfG ms′ Inv⊤ (k q)) → Wf bfG ms (iter k stIdle)
  wf-peer k h = wf-iter-bind (h stIdle) (λ _ q _ → h q)

  ------------------------------------------------------------------------
  -- The client peer
  ------------------------------------------------------------------------

  module Client (l : Link) (d : Dir) where

    -- one client step from each state.  `nowR`: an offered event in `bfG` carries no
    -- block (`λ ()`), or is the rely `receiveBF`, outside `bfG` (`⊥-elim`); a menu
    -- entry answered `nothing` is refuted on the offer equation (`()`).  `stepR`: the
    -- `with` mirrors the menu's own, and the relay in `stStreaming` hands the block's
    -- well-announcedness from `c-output` (rely) to `c-recvBF` (guarantee).
    cStep : ∀ {ms} q → WfR bfG ms Inv⊤ (clientStep l d q)

    -- stIdle: the api asks for a range or signals done; the wire is not offered
    cStep stIdle .nowR _ _ (sVis {at = (_ , sendBF _ _)}    refl ())
    cStep stIdle .nowR _ _ (sVis {at = (_ , receiveBF _ _)} refl ())
    cStep stIdle .nowR _ _ (sVis {at = (_ , doneBF _ _)}    refl ())
    cStep stIdle .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFRequestRange)} refl _) = λ ()
    cStep stIdle .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFClientDone)}   refl _) = λ ()
    cStep stIdle .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFStartBatch)}   refl ())
    cStep stIdle .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFNoBlocks)}     refl ())
    cStep stIdle .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFBlock)}        refl ())
    cStep stIdle .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFBatchDone)}    refl ())
    cStep stIdle .nowR _ _ (sVis {at = (_ , apiBFev _ _ recvBFBlock)}        refl ())
    cStep stIdle .nowR _ _ (sVis {at = (_ , apiBFev _ _ reqBFRange)}         refl ())
    cStep stIdle .stepR _ (sRet ())
    cStep stIdle .stepR _ (sSil ())
    cStep stIdle .stepR _ (sTau refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , sendBF _ _)}    refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , doneBF _ _)}    refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFStartBatch)} refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFNoBlocks)}   refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFBlock)}      refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFBatchDone)}  refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , apiBFev _ _ recvBFBlock)}      refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , apiBFev _ _ reqBFRange)}       refl ())
    cStep stIdle .stepR _ (sVis {at = (_ , apiBFev l′ d′ sendBFRequestRange)} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl →
            wfR-Output (λ _ _ → λ ()) (λ _ _ → wfR-Ret (λ _ → Poly.tt)) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    cStep stIdle .stepR _ (sVis {at = (_ , apiBFev l′ d′ sendBFClientDone)} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl →
            wfR-Output (λ _ _ → λ ()) (λ _ _ → wfR-Ret (λ _ → Poly.tt)) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    cStep stIdle .retR _ ()

    -- stBusy: only the wire is offered, and neither message carries a block
    cStep stBusy .nowR _ g (sVis {at = (_ , receiveBF _ _)} refl _) = ⊥-elim g
    cStep stBusy .nowR _ _ (sVis {at = (_ , sendBF _ _)}    refl ())
    cStep stBusy .nowR _ _ (sVis {at = (_ , apiBFev _ _ _)} refl ())
    cStep stBusy .nowR _ _ (sVis {at = (_ , doneBF _ _)}    refl ())
    cStep stBusy .stepR _ (sRet ())
    cStep stBusy .stepR _ (sSil ())
    cStep stBusy .stepR _ (sTau refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , sendBF _ _)}    refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , apiBFev _ _ _)} refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , doneBF _ _)}    refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , keepAlive _}    refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , chainSync _}    refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , txSubmission _} refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , leiosNotify _}  refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , leiosFetch _}   refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch (MsgRequestRange _)} refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch (MsgBlock _)}        refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch MsgBatchDone}        refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch MsgClientDone}       refl ())
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF l′ d′)} {a = _ , _ , _ , blockFetch MsgStartBatch} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl → wfR-Ret (λ _ → Poly.tt) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    cStep stBusy .stepR _ (sVis {at = (_ , receiveBF l′ d′)} {a = _ , _ , _ , blockFetch MsgNoBlocks} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl → wfR-Ret (λ _ → Poly.tt) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    cStep stBusy .retR _ ()

    -- stStreaming: THE RELAY — a block off the wire is delivered on the api
    cStep stStreaming .nowR _ g (sVis {at = (_ , receiveBF _ _)} refl _) = ⊥-elim g
    cStep stStreaming .nowR _ _ (sVis {at = (_ , sendBF _ _)}    refl ())
    cStep stStreaming .nowR _ _ (sVis {at = (_ , apiBFev _ _ _)} refl ())
    cStep stStreaming .nowR _ _ (sVis {at = (_ , doneBF _ _)}    refl ())
    cStep stStreaming .stepR _ (sRet ())
    cStep stStreaming .stepR _ (sSil ())
    cStep stStreaming .stepR _ (sTau refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , sendBF _ _)}    refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , apiBFev _ _ _)} refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , doneBF _ _)}    refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , keepAlive _}    refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , chainSync _}    refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , txSubmission _} refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , leiosNotify _}  refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , leiosFetch _}   refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch (MsgRequestRange _)} refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch MsgStartBatch}       refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch MsgNoBlocks}         refl ())
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch MsgClientDone}       refl ())
    -- the relay: `ok c-output` is the rely, `c-recvBF` names the guarantee
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF l′ d′)} {a = _ , _ , _ , blockFetch (MsgBlock b)} refl br) ok
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl →
            wfR-Output (λ le′ _ → λ { c-recvBF → wellAnnounced-mono le′ (ok c-output) })
                       (λ _ _ → wfR-Ret (λ _ → Poly.tt)) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    cStep stStreaming .stepR _ (sVis {at = (_ , receiveBF l′ d′)} {a = _ , _ , _ , blockFetch MsgBatchDone} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl → wfR-Ret (λ _ → Poly.tt) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    cStep stStreaming .retR _ ()

    -- stDone: √
    cStep stDone = wfR-Ret (λ _ → Poly.tt)

  -- THE CLIENT PEER, at the source alphabet
  wf-BFclient : ∀ {ms} (l : Link) (d : Dir) → Wf bfG ms (BFclientStClient l d)
  wf-BFclient l d = wf-peer (clientStep l d) (Client.cStep l d)

  ------------------------------------------------------------------------
  -- The server peer
  ------------------------------------------------------------------------

  module Server (l : Link) (d : Dir) where

    -- one server step from each state — the mirror image: the rely is the api's
    -- `sendBFBlock` (outside `bfG`), the guarantee the wire's `MsgBlock`
    sStep : ∀ {ms} q → WfR bfG ms Inv⊤ (serverStep l d q)

    -- stIdle: only the wire is offered; a range request or client-done arrives
    sStep stIdle .nowR _ g (sVis {at = (_ , receiveBF _ _)} refl _) = ⊥-elim g
    sStep stIdle .nowR _ _ (sVis {at = (_ , sendBF _ _)}    refl ())
    sStep stIdle .nowR _ _ (sVis {at = (_ , apiBFev _ _ _)} refl ())
    sStep stIdle .nowR _ _ (sVis {at = (_ , doneBF _ _)}    refl ())
    sStep stIdle .stepR _ (sRet ())
    sStep stIdle .stepR _ (sSil ())
    sStep stIdle .stepR _ (sTau refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , sendBF _ _)}    refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , apiBFev _ _ _)} refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , doneBF _ _)}    refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , keepAlive _}    refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , chainSync _}    refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , txSubmission _} refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , leiosNotify _}  refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , leiosFetch _}   refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch MsgStartBatch} refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch MsgNoBlocks}   refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch (MsgBlock _)}  refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF _ _)} {a = _ , _ , _ , blockFetch MsgBatchDone}  refl ())
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF l′ d′)} {a = _ , _ , _ , blockFetch (MsgRequestRange _)} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl →
            wfR-Output (λ _ _ → λ ()) (λ _ _ → wfR-Ret (λ _ → Poly.tt)) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    sStep stIdle .stepR _ (sVis {at = (_ , receiveBF l′ d′)} {a = _ , _ , _ , blockFetch MsgClientDone} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl →
            wfR-Prefix (λ _ _ _ → λ ()) (λ _ _ _ → wfR-Ret (λ _ → Poly.tt)) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    sStep stIdle .retR _ ()

    -- stBusy: the api opens or declines a batch; neither wire message carries a block
    sStep stBusy .nowR _ _ (sVis {at = (_ , sendBF _ _)}    refl ())
    sStep stBusy .nowR _ _ (sVis {at = (_ , receiveBF _ _)} refl ())
    sStep stBusy .nowR _ _ (sVis {at = (_ , doneBF _ _)}    refl ())
    sStep stBusy .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFStartBatch)}   refl _) = λ ()
    sStep stBusy .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFNoBlocks)}     refl _) = λ ()
    sStep stBusy .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFRequestRange)} refl ())
    sStep stBusy .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFClientDone)}   refl ())
    sStep stBusy .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFBlock)}        refl ())
    sStep stBusy .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFBatchDone)}    refl ())
    sStep stBusy .nowR _ _ (sVis {at = (_ , apiBFev _ _ recvBFBlock)}        refl ())
    sStep stBusy .nowR _ _ (sVis {at = (_ , apiBFev _ _ reqBFRange)}         refl ())
    sStep stBusy .stepR _ (sRet ())
    sStep stBusy .stepR _ (sSil ())
    sStep stBusy .stepR _ (sTau refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , sendBF _ _)}    refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , receiveBF _ _)} refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , doneBF _ _)}    refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFRequestRange)} refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFClientDone)}   refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFBlock)}        refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFBatchDone)}    refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , apiBFev _ _ recvBFBlock)}        refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , apiBFev _ _ reqBFRange)}         refl ())
    sStep stBusy .stepR _ (sVis {at = (_ , apiBFev l′ d′ sendBFStartBatch)} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl →
            wfR-Output (λ _ _ → λ ()) (λ _ _ → wfR-Ret (λ _ → Poly.tt)) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    sStep stBusy .stepR _ (sVis {at = (_ , apiBFev l′ d′ sendBFNoBlocks)} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl →
            wfR-Output (λ _ _ → λ ()) (λ _ _ → wfR-Ret (λ _ → Poly.tt)) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    sStep stBusy .retR _ ()

    -- stStreaming: THE RELAY — a block off the api goes onto the wire
    sStep stStreaming .nowR _ g (sVis {at = (_ , apiBFev _ _ sendBFBlock)} refl _) = ⊥-elim g
    sStep stStreaming .nowR _ _ (sVis {at = (_ , sendBF _ _)}    refl ())
    sStep stStreaming .nowR _ _ (sVis {at = (_ , receiveBF _ _)} refl ())
    sStep stStreaming .nowR _ _ (sVis {at = (_ , doneBF _ _)}    refl ())
    sStep stStreaming .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFBatchDone)}    refl _) = λ ()
    sStep stStreaming .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFRequestRange)} refl ())
    sStep stStreaming .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFClientDone)}   refl ())
    sStep stStreaming .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFStartBatch)}   refl ())
    sStep stStreaming .nowR _ _ (sVis {at = (_ , apiBFev _ _ sendBFNoBlocks)}     refl ())
    sStep stStreaming .nowR _ _ (sVis {at = (_ , apiBFev _ _ recvBFBlock)}        refl ())
    sStep stStreaming .nowR _ _ (sVis {at = (_ , apiBFev _ _ reqBFRange)}         refl ())
    sStep stStreaming .stepR _ (sRet ())
    sStep stStreaming .stepR _ (sSil ())
    sStep stStreaming .stepR _ (sTau refl ())
    sStep stStreaming .stepR _ (sVis {at = (_ , sendBF _ _)}    refl ())
    sStep stStreaming .stepR _ (sVis {at = (_ , receiveBF _ _)} refl ())
    sStep stStreaming .stepR _ (sVis {at = (_ , doneBF _ _)}    refl ())
    sStep stStreaming .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFRequestRange)} refl ())
    sStep stStreaming .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFClientDone)}   refl ())
    sStep stStreaming .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFStartBatch)}   refl ())
    sStep stStreaming .stepR _ (sVis {at = (_ , apiBFev _ _ sendBFNoBlocks)}     refl ())
    sStep stStreaming .stepR _ (sVis {at = (_ , apiBFev _ _ recvBFBlock)}        refl ())
    sStep stStreaming .stepR _ (sVis {at = (_ , apiBFev _ _ reqBFRange)}         refl ())
    -- the relay: `ok c-sendBF` is the rely, `c-input` names the guarantee
    sStep stStreaming .stepR _ (sVis {at = (_ , apiBFev l′ d′ sendBFBlock)} refl br) ok
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl →
            wfR-Output (λ le′ _ → λ { c-input → wellAnnounced-mono le′ (ok c-sendBF) })
                       (λ _ _ → wfR-Ret (λ _ → Poly.tt)) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    sStep stStreaming .stepR _ (sVis {at = (_ , apiBFev l′ d′ sendBFBatchDone)} refl br) _
      with l′ ≟ l | d′ ≟ d
    ... | yes refl | yes refl = case br of λ { refl →
            wfR-Output (λ _ _ → λ ()) (λ _ _ → wfR-Ret (λ _ → Poly.tt)) }
    ... | no _     | _        = case br of λ ()
    ... | yes refl | no _     = case br of λ ()
    sStep stStreaming .retR _ ()

    -- stDone: √
    sStep stDone = wfR-Ret (λ _ → Poly.tt)

  -- THE SERVER PEER, at the source alphabet
  wf-BFserver : ∀ {ms} (l : Link) (d : Dir) → Wf bfG ms (BFserverStClient l d)
  wf-BFserver l d = wf-peer (serverStep l d) (Server.sStep l d)

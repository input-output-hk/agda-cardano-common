{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S5 AT THE SYSTEM LEVEL: TRANSACTION ORIGIN OF
-- THE WHOLE N-NODE LEIOS-PROTOTYPE NETWORK running `nodeLogicL` at every
-- node behind the prototype peer bundle `PeersP.nodeBundleP`, over the
-- CONCRETE per-link multiplexer `NetCommon.NetworkLinkBreakableA`, with the
-- io channels hidden.
--
-- WHAT IT SAYS.  No node of the network ever puts a transaction in its
-- mempool unless THAT NODE was handed that transaction by the environment,
-- or asked for its hash AT ONE OF ITS OWN ENDPOINTS.  "At that node" is a
-- fact about the discipline and not about the quantifier: `TxOrigin`'s
-- re-keying mints `((l , d) , txHash tx)` at `env l d envSubmit` —
-- node-local, since `submitEv n` fires at `homeOf n` — and keys the two wire
-- mints by the node whose thread drives the channel (`homeOpp (l , d)` at
-- `apiTS l d sendTSRequestTxsPipelined`, whose requester runs at
-- `opposite d`; `homeAt (l , d)` at `apiLP l d lfpSendBlockTxsRequest`,
-- whose Notify client runs at `d`), while a `store l d stPutTx ! tx` demands
-- `((l , d) , txHash tx)`.  `homeOf` is injective (`TxOrigin.homeOf-inj`),
-- so a submission or a request at node X cannot open a gate at node Y even
-- though every node's env, api and store channels sit in the same composite.
--
-- WHAT IT DOES NOT SAY — `TxOrigin`'s deliberate gaps, unchanged by the lift,
-- AND ITS TWO HONEST LIMITS.  Read that module's header; the two that must
-- travel with any quotation of this theorem are:
--   * NO TRANSACTION IN THIS MODEL EVER REACHES CONSENSUS.  `ebTxs` is a
--     `LeiosParams` field fixed independently of any node's mempool, and
--     nothing builds an EB or a ranking block out of `Mem`; the mempool's
--     only readers are the two wire servers.  S5 is DIFFUSION HYGIENE, not
--     the analogue of S1 — S1 guards the store the voter actually reads.
--   * THE KEY SPACE SATURATES AT THE SHIPPED LINE (`Tx = TxHash = Bool`,
--     `txHash = id`), so at `leiosSystemL` two `envSubmit` events mint the
--     whole per-endpoint key space.  Parity with S1, whose `EBHash` is `Bool`
--     too, not a new defect.
-- Beyond those: `txHash` is nowhere assumed injective, so the guards fix the
-- HASH and not the CONTENT; the minted set is append-only and unpaired, so
-- one request licenses unboundedly many later deposits of those hashes at
-- that node; and it says nothing about the block, EB-entry, EB-body or vote
-- stores.  Nothing about liveness — no module exhibits a good node actually
-- reaching `stPutTx` — and nothing about divergence: `⊑T` is a safety order.
--
-- THE PREMISES.  NONE.  `TxOrigin.Generic` takes exactly the five arguments
-- `NodeLogicL.Generic` takes, all of them data about the parameter set; there
-- is no monotonicity premise (that is S3's), no voter retraction (that is
-- S2′'s) and no link-configuration premise: like S1/S2′/S3 and unlike S0,
-- this theorem needs no copy→concrete medium transport, so
-- `AnnounceSafeConcrete.LinkCfgWf` never arises.  `txSoundLT` below is
-- therefore unconditional at every parameter set, and `leiosTxSoundLT` is the
-- same statement at the shipped three-node line.
--
-- WHAT IS REUSED VERBATIM FROM `Leios.BodySystemL`: `sep-io`, `hideCov-full`,
-- `med-noNeed`, `wf-med`, `noRet-system`, and the proof TERMS of
-- `wf-nodeC`/`wf-system`/`txSoundSys`.  `hideKeep-io`'s nineteen clauses are
-- not free, because its type mentions `next` hence the instance's `mints`;
-- they are mechanical here too — `txMints` fires only on `env _ _ envSubmit`,
-- `apiTS _ _ sendTSRequestTxsPipelined` and
-- `apiLP _ _ lfpSendBlockTxsRequest`, none of which is in `ioES`, so the only
-- non-absurd clauses are `input`/`output`, where the catch-all reduces to
-- `[]`.  With this file the hoist is owed by a SEVENTH consumer; it is still
-- not taken, because taking it would rewrite every green system module at
-- once and the premise it needs ("`mints` is empty on `input` and `output`")
-- is one line per instance either way.
--
-- THE ONE THING S5 NEEDED THAT NO EARLIER DISCIPLINE DID: TWO membership
-- threads, not one.  S1 spends `Topology.endpoints-sound` at a single leaf
-- (`wf-lnClient`); S5 spends it at `wf-lnClient` AND `wf-tsPull`, and at the
-- latter through `opposite`'s involutivity, because the TxSubmission
-- requester drives the opposite direction.  Both are delivered to their leaf
-- by `BlockProvenanceWfR.wf-⦀⁺∈` from the one fold.  Its SUBMISSION mint is
-- node-local, so record η closes that third of the discipline definitionally.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.TxSystemL where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (AnyTypes; ExtI)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Topology using (Topology)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Net as N
import Cardano_network.Data as D
import CSP.Operators as O
import Cardano_network.NetCommon as NC
import Cardano_network.ApiAlphabet as AA
import Cardano_network.Parametric.BlockProvenanceSafe as BPS
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.TxOrigin as TO
import Cardano_network.Parametric.Leios.LeiosInstanceL as LIL
open import Cardano_network.Base using (Dir)

-- the system level of S5, parametric in the same five arguments `TxOrigin.Generic`
-- takes, so every leaf fact below is literally that module's
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open N p
    using ( Link; Net_Api; Net_Api-≟
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; apiLP; store; env; break )
  open D p using (Payload)
  open NC p using (ioES; NetworkLinkBreakableA)
  open Topology t using (Node; numNodes-1)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (EventSet)
  open import Cardano_network.Parametric.Node p t apiES
    using (Proc; nodeWith; linkBundlesWith; systemOfWithNode)
  open import Cardano_network.Parametric.Leios.PeersP p using (nodeBundleP)
  open import Cardano_network.MediumEquivA p
    using (classify; linkAlphaA; oo-breakableNetLinkA)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using ( NoRet; OffersOnly; OffersOnly-mono; OffersOnly-⦀Fin; unionAlpha )
  open import Semantics.Failures
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⊑T_)
  open BPS.Generic p t apiES using (NoRet-ParR; NoRet-Hide; NoRet-⦀Fin⁺)
  open NLL.Generic p lp t apiES voterOf using (nodeLogicL; st₀)
  -- S5's discipline, which re-exports (`public`) the shared leaves — `fullα`, the
  -- vacuous leaf, `sep-api`, the prototype peer bundle — the carrier names it uses, and
  -- the four only a system fold needs, so the `Wf` folded below is the very one
  -- `txSound` is proved with and no second `BlockProvenance.Carrier` application arises
  open TO.Generic p lp t apiES voterOf
    using ( Minted; TxKey; txCarries; txWA; txNext; txNext-⊆; txMints
          ; needs-store; TxSpecT; wf→osafe; osafe→⊑T; wf-logic; noRet-logic
          ; fullα; noNeed; wf-free; sep-api; wf-linkBundlesP
          ; Wf; wf-mono-G; Sep; wf-Par
          ; wf-⦀Fin⁺; HideCov; HideKeep; wf-Hide )

  ------------------------------------------------------------------------
  -- The three side conditions of the system fold
  --
  -- All three are `BodySystemL`'s, which that file's closing note promised would
  -- transfer unchanged.  Nothing below mentions `stPutTx`, `envSubmit`,
  -- `sendTSRequestTxsPipelined` or `lfpSendBlockTxsRequest`.
  ------------------------------------------------------------------------

  -- SEP AT THE IO RENDEZVOUS: both the medium and the node fold carry the FULL
  -- guarantee alphabet, so there is nothing to reroute — the same two-liner as
  -- `OriginLeaves.sep-api`
  sep-io : Sep ioES fullα fullα
  sep-io = (λ _ _ _ → tt) , (λ _ _ _ → tt)

  -- THE COVERAGE CONDITION OF HIDING: a hidden carrying label must be guaranteed by the
  -- process under the `∖`, and on the full alphabet every label is
  hideCov-full : HideCov ioES fullα
  hideCov-full _ _ = tt

  -- NO IO CHANNEL MINTS, so hiding one leaves the minted set alone.  One clause per
  -- `Net_Api` constructor, because `ioSet` does not reduce until the constructor is
  -- known.  `env`, `apiTS` and `apiLP` — the three channels S5 mints at — are absurd
  -- here because none is in `ioES`, so only `input`/`output` survive and there `txMints`
  -- is `[]`.
  hideKeep-io : HideKeep ioES
  hideKeep-io {e = input  _ _ _} _ _  = λ q → q
  hideKeep-io {e = output _ _ _} _ _  = λ q → q
  hideKeep-io {e = sndmsg _ _ _} _ ()
  hideKeep-io {e = rcvmsg _ _ _} _ ()
  hideKeep-io {e = tx     _ _ _} _ ()
  hideKeep-io {e = sndack _ _ _} _ ()
  hideKeep-io {e = rcvack _ _ _} _ ()
  hideKeep-io {e = ack    _ _ _} _ ()
  hideKeep-io {e = done   _ _ _} _ ()
  hideKeep-io {e = apiCS  _ _ _} _ ()
  hideKeep-io {e = apiBF  _ _ _} _ ()
  hideKeep-io {e = apiTS  _ _ _} _ ()
  hideKeep-io {e = apiKA  _ _ _} _ ()
  hideKeep-io {e = apiLN  _ _ _} _ ()
  hideKeep-io {e = apiLF  _ _ _} _ ()
  hideKeep-io {e = apiLP  _ _ _} _ ()
  hideKeep-io {e = store  _ _ _} _ ()
  hideKeep-io {e = env    _ _ _} _ ()
  hideKeep-io {e = break  _}     _ ()

  ------------------------------------------------------------------------
  -- The medium
  ------------------------------------------------------------------------

  -- A LINK-CLASSIFIED EVENT CARRIES NO KEY: a carrying channel is a `store` channel
  -- (`needs-store`), and `MediumEquivA.classify` sends every `store` channel — every
  -- node-local channel, in fact — to `nothing`
  med-noNeed : ∀ at a → unionAlpha linkAlphaA at a → noNeed at a
  med-noNeed (X , e) a (i , k , q) c with needs-store {e = e} c
  ... | _ , _ , _ , refl = case q of λ ()

  -- THE CONCRETE PER-LINK MULTIPLEXER IS A VACUITY, at every guarantee alphabet and
  -- every minted set.  THIS is why S5, like S1/S2′/S3, needs no copy→concrete transport.
  wf-med : ∀ {ms} → Wf fullα ms NetworkLinkBreakableA
  wf-med = wf-free (OffersOnly-mono med-noNeed (OffersOnly-⦀Fin oo-breakableNetLinkA))

  ------------------------------------------------------------------------
  -- `noTick`
  ------------------------------------------------------------------------

  -- THE WHOLE NETWORK NEVER RETURNS, over ANY medium and ANY peer-bundle builder: hide,
  -- medium-right, node fold head, logic-right.  Verbatim `BodySystemL.noRet-system`.
  noRet-system : ∀ (mk : Link → Dir → Dir → Proc) med (lg : Node → Proc)
               → (∀ n → NoRet (lg n)) → NoRet (systemOfWithNode (nodeWith mk) med lg)
  noRet-system mk med lg h =
    NoRet-Hide ioES
      (NoRet-ParR ioES (NoRet-⦀Fin⁺ numNodes-1 (NoRet-ParR apiES (h fzero))))

  ------------------------------------------------------------------------
  -- The statement, and the assembly
  ------------------------------------------------------------------------

  -- THE SHIPPED NETWORK: the N-node Leios-prototype system this file is about, named so
  -- the headline can quote it without re-opening `Node`
  leiosNet : Proc
  leiosNet =
    systemOfWithNode (nodeWith nodeBundleP) NetworkLinkBreakableA (λ n → nodeLogicL n st₀)

  -- ONE LEIOS NODE on the full alphabet: the twelve prototype peers against the
  -- Linear-Leios logic, `sep-api` discharging the api rendezvous because both sides
  -- carry the full alphabet
  wf-nodeC : ∀ {ms} n → Wf fullα ms (nodeWith nodeBundleP n (nodeLogicL n st₀))
  wf-nodeC n =
    wf-mono-G (λ _ _ _ → inj₁ tt)
      (wf-Par apiES sep-api (wf-linkBundlesP n) (wf-logic n))

  -- THE WHOLE NETWORK: the nodes interleaved, synchronised with the concrete medium on
  -- `ioES`, io hidden.  Three one-line side conditions and two folds — no alphabet
  -- bookkeeping, because everything lives on `fullα`.
  wf-system : ∀ {ms} → Wf fullα ms leiosNet
  wf-system =
    wf-Hide ioES hideCov-full hideKeep-io
      (wf-mono-G (λ _ _ _ → inj₁ tt)
        (wf-Par ioES sep-io wf-med (wf-⦀Fin⁺ numNodes-1 wf-nodeC)))

  -- THE STATEMENT of S5 at the system level, over the CONCRETE per-link multiplexer
  TxSoundLT : Set₁
  TxSoundLT = TxSpecT ⊑T leiosNet

  -- S5, PROVED OF THE WHOLE NETWORK.  `wf→osafe` turns the one `Wf fullα []` fact into
  -- an `OSafe []` fact — `noTick` coming from `noRet-system` over the per-node
  -- `noRet-logic` — and `osafe→⊑T` turns that into the refinement.
  txSoundSys : TxSoundLT
  txSoundSys =
    osafe→⊑T (wf→osafe wf-system
                (noRet-system nodeBundleP NetworkLinkBreakableA _ noRet-logic))

------------------------------------------------------------------------
-- THE THEOREM, at the shared api alphabet
------------------------------------------------------------------------

-- S5 AT THE SYSTEM LEVEL, for every parameter set, every topology and every voter map:
-- no node of the whole N-node Leios-prototype network puts a transaction in its mempool
-- that it was neither handed by the environment nor asked for at one of its OWN
-- endpoints.  There is no premise at all — no oracle, no voter retraction and no link
-- configuration.  READ `TxOrigin`'s header for the two honest limits: this is a
-- diffusion-hygiene statement, and the shipped instance's key space is two keys wide.
txSoundLT : ∀ (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
              (voterOf : Topology.Node t → Params.VoterId p)
          → Generic.TxSoundLT p lp t (AA.apiES p) voterOf
txSoundLT p lp t voterOf = Generic.txSoundSys p lp t (AA.apiES p) voterOf

------------------------------------------------------------------------
-- The shipped Leios line
------------------------------------------------------------------------

open import Semantics.Failures
  {E = N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams)}
  {I = ExtI (N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams))} using (_⊑T_)

-- S5's discipline at the shipped three-node Linear-Leios line, where `VoterId = Node` and
-- the voter map is the identity
module TOLS = TO.Generic LIL.leiosLParams LIL.leiosLP LIL.leiosLLine
                         (AA.apiES LIL.leiosLParams) (λ n → n)

-- S5 AT THE SYSTEM LEVEL FOR THE SHIPPED LEIOS LINE, PREMISE-FREE, stated against the
-- shipped witness `LeiosInstanceL.leiosSystemL` itself: in the three-node line, every
-- node running the whole Linear-Leios logic from empty stores behind the twelve prototype
-- peers, over the concrete per-link multiplexer with io hidden, no node ever puts a
-- transaction in its mempool unless the environment submitted that transaction to it or
-- it asked for that transaction's hash at one of its own endpoints.
leiosTxSoundLT : TOLS.TxSpecT ⊑T LIL.leiosSystemL
leiosTxSoundLT =
  txSoundLT LIL.leiosLParams LIL.leiosLP LIL.leiosLLine (λ n → n)

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S2′ AT THE SYSTEM LEVEL: BLOB ORIGIN OF THE
-- WHOLE N-NODE LEIOS-PROTOTYPE NETWORK running `nodeLogicL` at every node
-- behind the prototype peer bundle `PeersP.nodeBundleP`, over the CONCRETE
-- per-link multiplexer `NetCommon.NetworkLinkBreakableA`, with the io
-- channels hidden.
--
-- WHAT IT SAYS.  No node of the network ever deposits a vote blob
-- attributed to ANOTHER node's voter unless a Notify votes delivery AT ONE
-- OF THAT NODE'S OWN ENDPOINTS carried that exact blob.  "At that node" is
-- a fact about the discipline and not about the quantifier: `BlobOrigin`'s
-- re-keying mints `(homeAt (l , d) , v)` at `apiLP l d lnpRecvVotes` and
-- demands `((l , d) , v)` at `store l d stPutVote`, and `homeOf` is
-- injective (`BlobOrigin.homeOf-inj`), so a delivery received at node X
-- cannot open a gate at node Y even though both nodes' api and store
-- channels sit in the same composite.
--
-- WHAT IT DOES NOT SAY — `BlobOrigin`'s four deliberate gaps, unchanged by
-- the lift: a blob a node fabricates in its OWN name is free (that is S2,
-- `VoteSound`); so is one it received and relabelled into its own name;
-- "delivered" means only that an `lnpRecvVotes` event happened, never that
-- the named voter signed it; and a blob naming a voter id NO node owns
-- passes the `atVoter` disjunct freely wherever `nodeOf` happens to send it
-- (empty at `LeiosInstanceL`, where `VoterId = Node` and `nodeOf = id`).
-- Nothing about liveness, and nothing about divergence: `⊑T` is a safety
-- order.
--
-- THE PREMISES.  None beyond `BlobOrigin.Generic`'s own two parameters —
-- the voter-to-node map `nodeOf` and the round-trip law
-- `nodeOf (voterOf n) ≡ n`.  Those are DATA about the parameter set, not a
-- hypothesis about the logic, and at the shipped line they are the identity
-- and `refl`, so `leiosBlobSoundLT` at the bottom is unconditional.  There
-- is no monotonicity premise (that is S3's), and no link-configuration
-- premise: unlike S0, this theorem needs no copy→concrete medium transport,
-- so `AnnounceSafeConcrete.LinkCfgWf` never arises.
--
-- WHAT IS REUSED VERBATIM FROM `Leios.CertSystemL` — the pilot's closing
-- note said these are discipline-parametric and they are: `sep-io`,
-- `hideCov-full`, `med-noNeed`, `wf-med`, `noRet-system`, and the proof
-- TERMS of `wf-nodeC`/`wf-system`/`blobSoundSys`.  `hideKeep-io` is the one
-- that is not free, because its type mentions `next` hence the instance's
-- `mints`; its nineteen clauses are mechanical here too — `blobMints` fires
-- only on `apiLP _ _ lnpRecvVotes`, which is not in `ioES`, so the only
-- non-absurd clauses are `input`/`output`, where the catch-all reduces to
-- `[]`.  The hoist the pilot flagged ("`mints` is empty on `input` and
-- `output`") is now owed by a SECOND consumer and is left for the third.
--
-- THE ONE THING S2′ NEEDED THAT S3 DID NOT.  S3's mint is at a `store`
-- channel at `homeOf n`, so record η closed the endpoint bookkeeping
-- definitionally.  S2′'s mint is at a per-endpoint `apiLP` channel, so the
-- leaf must know that the receiving endpoint belongs to the depositing
-- node — `Topology.endpoints-sound`.  That fact is not available to a fold
-- whose hypothesis is quantified over the whole index type, which is why
-- `BlockProvenanceWfR.Body` gained `wf-⦀⁺∈`: the same recursion as
-- `wf-⦀⁺`, with each leaf handed its own membership.  S1/S2/S4 inherit it.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.BlobSystemL where

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
import Cardano_network.Parametric.Leios.BlobOrigin as BO
import Cardano_network.Parametric.Leios.LeiosInstanceL as LIL
open import Cardano_network.Base using (Dir)

-- the system level of S2′, parametric in the same seven arguments `BlobOrigin.Generic`
-- takes, so every leaf fact below is literally that module's
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p)
  (nodeOf : Params.VoterId p → Topology.Node t)
  (nodeOf-voterOf : ∀ n → nodeOf (voterOf n) ≡ n) where

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
  -- S2′'s discipline, which re-exports (`public`) both the shared leaves — `fullα`, the
  -- vacuous leaf, `sep-api`, the prototype peer bundle — and the carrier names it uses,
  -- so the `Wf` folded below is the very one `blobSound` is proved with
  -- … including the four carrier names `BlobOrigin` does not itself use, which it now
  -- re-exports, so `wf-Hide`/`wf-⦀Fin⁺` fold the very `Wf` opened here and no second
  -- application of `BlockProvenance.Carrier` is needed
  open BO.Generic p lp t apiES voterOf nodeOf nodeOf-voterOf
    using ( Minted; BlobKey; blobCarries; blobWA; blobNext; blobNext-⊆; blobMints
          ; needs-store; BlobSpecT; wf→osafe; osafe→⊑T; wf-logic; noRet-logic
          ; fullα; noNeed; wf-free; sep-api; wf-linkBundlesP
          ; Wf; wf-mono-G; Sep; wf-Par
          ; wf-⦀Fin⁺; HideCov; HideKeep; wf-Hide )

  ------------------------------------------------------------------------
  -- The three side conditions of the system fold
  --
  -- All three are `CertSystemL`'s, which that file's closing note promised would
  -- transfer unchanged.  Nothing below mentions `stPutVote`, `lnpRecvVotes` or
  -- `atVoter`.
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
  -- known.  `apiLP` — the ONE channel S2′ mints at — is absurd here because it is not
  -- in `ioES`, so only `input`/`output` survive and there `blobMints` is `[]`.
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
  -- every minted set.  THIS is why S2′, like S3, needs no copy→concrete transport.
  wf-med : ∀ {ms} → Wf fullα ms NetworkLinkBreakableA
  wf-med = wf-free (OffersOnly-mono med-noNeed (OffersOnly-⦀Fin oo-breakableNetLinkA))

  ------------------------------------------------------------------------
  -- `noTick`
  ------------------------------------------------------------------------

  -- THE WHOLE NETWORK NEVER RETURNS, over ANY medium and ANY peer-bundle builder: hide,
  -- medium-right, node fold head, logic-right.  Verbatim `CertSystemL.noRet-system`.
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

  -- THE STATEMENT of S2′ at the system level, over the CONCRETE per-link multiplexer
  BlobSoundLT : Set₁
  BlobSoundLT = BlobSpecT ⊑T leiosNet

  -- S2′, PROVED OF THE WHOLE NETWORK.  `wf→osafe` turns the one `Wf fullα []` fact into
  -- an `OSafe []` fact — `noTick` coming from `noRet-system` over the per-node
  -- `noRet-logic` — and `osafe→⊑T` turns that into the refinement.
  blobSoundSys : BlobSoundLT
  blobSoundSys =
    osafe→⊑T (wf→osafe wf-system
                (noRet-system nodeBundleP NetworkLinkBreakableA _ noRet-logic))

------------------------------------------------------------------------
-- THE THEOREM, at the shared api alphabet
------------------------------------------------------------------------

-- S2′ AT THE SYSTEM LEVEL, for every parameter set, every topology, every voter map and
-- every voter-to-node retraction: no node of the whole N-node Leios-prototype network
-- deposits a vote blob in another voter's name unless a Notify votes delivery at one of
-- THAT node's own endpoints carried it.  There is no oracle premise and no
-- link-configuration premise; `nodeOf` and its round-trip law are the only extra data,
-- and they are `BlobOrigin.Generic`'s own.
blobSoundLT : ∀ (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
                (voterOf : Topology.Node t → Params.VoterId p)
                (nodeOf : Params.VoterId p → Topology.Node t)
            → (nodeOf-voterOf : ∀ n → nodeOf (voterOf n) ≡ n)
            → Generic.BlobSoundLT p lp t (AA.apiES p) voterOf nodeOf nodeOf-voterOf
blobSoundLT p lp t voterOf nodeOf nodeOf-voterOf =
  Generic.blobSoundSys p lp t (AA.apiES p) voterOf nodeOf nodeOf-voterOf

------------------------------------------------------------------------
-- The shipped Leios line
------------------------------------------------------------------------

open import Semantics.Failures
  {E = N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams)}
  {I = ExtI (N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams))} using (_⊑T_)

-- S2′'s discipline at the shipped three-node Linear-Leios line: `VoterId = Node`, so
-- the voter map and its inverse are both the identity and the round-trip law is `refl`
module BOLS = BO.Generic LIL.leiosLParams LIL.leiosLP LIL.leiosLLine
                         (AA.apiES LIL.leiosLParams) (λ n → n) (λ u → u) (λ n → refl)

-- S2′ AT THE SYSTEM LEVEL FOR THE SHIPPED LEIOS LINE, PREMISE-FREE, stated against the
-- shipped witness `LeiosInstanceL.leiosSystemL` itself: in the three-node line, every
-- node running the whole Linear-Leios logic from empty stores behind the twelve
-- prototype peers, over the concrete per-link multiplexer with io hidden, no node ever
-- deposits a vote blob attributed to another node's voter unless a Notify votes delivery
-- at one of its own endpoints carried that exact blob.
leiosBlobSoundLT : BOLS.BlobSpecT ⊑T LIL.leiosSystemL
leiosBlobSoundLT =
  blobSoundLT LIL.leiosLParams LIL.leiosLP LIL.leiosLLine (λ n → n) (λ u → u) (λ n → refl)

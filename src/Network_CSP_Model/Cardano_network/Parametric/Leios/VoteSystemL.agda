{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S2 AT THE SYSTEM LEVEL: VOTE SOUNDNESS OF THE
-- WHOLE N-NODE LEIOS-PROTOTYPE NETWORK running `nodeLogicL` at every node
-- behind the prototype peer bundle `PeersP.nodeBundleP`, over the CONCRETE
-- per-link multiplexer `NetCommon.NetworkLinkBreakableA`, with the io
-- channels hidden.
--
-- WHAT IT SAYS.  No node of the network ever deposits a vote blob `v` in its
-- vote store unless, AT ONE OF THAT NODE'S OWN ENDPOINTS, either a Notify
-- votes delivery carried `v`, or THAT NODE read a ranking block `b` with
-- `rbHash b ≡ blobRb v` out of its own block store AND read the body of the
-- EB that `b` announces.  "That node" is a fact about the discipline and not
-- about the quantifier: `VoteSound`'s re-keying mints `((l , d) , kRb b)` at
-- `store l d (stGetAt k)` and `((l , d) , kBody h)` at
-- `store l d (stGetBody h)` — both node-local, since `getAtEv n`,
-- `getBodyEv n` and `putVoteEv n` all fire at `homeOf n` — and
-- `(homeAt (l , d) , kRelay v)` at `apiLP l d lnpRecvVotes`, while
-- `voteκ`'s first conjunct tests the key's endpoint against the deposit's.
-- `homeOf` is injective (`VoteSound.homeOf-inj`), so a read or a delivery at
-- node X cannot open a gate at node Y even though every node's store and api
-- channels sit in the same composite.
--
-- WHAT IT DOES NOT SAY — `VoteSound`'s deliberate gaps, unchanged by the
-- lift.  IT IS NOT A VALIDITY STATEMENT: the prototype's vote blob carries no
-- verdict at all, only a voter and the ranking block it endorses, so S2 is a
-- statement about WORK DONE and nothing more.  A RELAYED blob is free — that
-- a named voter really cast it is S2′ (`Leios.BlobSystemL`), and nothing here
-- says the voter named is the depositing node.  The body read is keyed by the
-- hash the read ASKED FOR, not by `ebHash eb`; the two agree at the composite
-- but the discipline does not prove it.  The minted set is append-only and
-- unpaired, so one pair of reads licenses unboundedly many later deposits of
-- that blob at that node.  Nothing about liveness, and nothing about
-- divergence: `⊑T` is a safety order.
--
-- THE PREMISES.  NONE.  `VoteSound.Generic` takes exactly the five arguments
-- `NodeLogicL.Generic` takes, all of them data about the parameter set; there
-- is no monotonicity premise (that is S3's), no voter retraction (that is
-- S2′'s) and no link-configuration premise: unlike S0, this theorem needs no
-- copy→concrete medium transport, so `AnnounceSafeConcrete.LinkCfgWf` never
-- arises.  `voteSoundLT` below is therefore unconditional at every parameter
-- set, and `leiosVoteSoundLT` is the same statement at the shipped three-node
-- line.
--
-- WHAT IS REUSED VERBATIM FROM `Leios.CertSystemL`, `Leios.BlobSystemL`,
-- `Leios.BodySystemL` and `Leios.CertRbSystemL`: `sep-io`, `hideCov-full`,
-- `med-noNeed`, `wf-med`, `noRet-system`, and the proof TERMS of
-- `wf-nodeC`/`wf-system`/`voteSoundSys`.  `hideKeep-io`'s nineteen clauses are
-- not free, because its type mentions `next` hence the instance's `mints`;
-- they are mechanical here too — `voteMints` fires only on
-- `store _ _ (stGetAt _)`, `store _ _ (stGetBody _)` and
-- `apiLP _ _ lnpRecvVotes`, none of which is in `ioES`, so the only
-- non-absurd clauses are `input`/`output`, where the catch-all reduces to
-- `[]`.  With this file every one of the five has its own copy, and the hoist
-- into `OriginLeaves.Leaves` — one premise, "`mints` is empty on `input` and
-- `output`" — is now plainly worth taking; it is left out of this brief
-- because it would touch all five green modules at once.
--
-- THE ONE THING S2 NEEDED THAT S3 DID NOT, and S2′/S1/S4 did: its relay mint
-- is at a per-endpoint `apiLP` channel, so the leaf must know that the
-- receiving endpoint belongs to the depositing node —
-- `Topology.endpoints-sound`, delivered to the leaf by
-- `BlockProvenanceWfR.wf-⦀⁺∈`.  Its two STORE mints are node-local, so record
-- η closes that half definitionally, exactly as S3's store mint does.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.VoteSystemL where

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
import Cardano_network.Parametric.Leios.VoteSound as VS
import Cardano_network.Parametric.Leios.LeiosInstanceL as LIL
open import Cardano_network.Base using (Dir)

-- the system level of S2, parametric in the same five arguments `VoteSound.Generic`
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
  -- S2's discipline, which re-exports (`public`) the shared leaves — `fullα`, the
  -- vacuous leaf, `sep-api`, the prototype peer bundle — the carrier names it uses, and
  -- the four only a system fold needs, so the `Wf` folded below is the very one
  -- `voteSound` is proved with and no second `BlockProvenance.Carrier` application arises
  open VS.Generic p lp t apiES voterOf
    using ( Minted; VoteKeyE; VoteNeed; voteCarries; voteWA; voteNext; voteNext-⊆; voteMints
          ; needs-store; VoteSpecT; wf→osafe; osafe→⊑T; wf-logic; noRet-logic
          ; fullα; noNeed; wf-free; sep-api; wf-linkBundlesP
          ; Wf; wf-mono-G; Sep; wf-Par
          ; wf-⦀Fin⁺; HideCov; HideKeep; wf-Hide )

  ------------------------------------------------------------------------
  -- The three side conditions of the system fold
  --
  -- All three are `CertSystemL`'s, which that file's closing note promised would
  -- transfer unchanged.  Nothing below mentions `stPutVote`, the two store reads or
  -- `lnpRecvVotes`.
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
  -- known.  `store` and `apiLP` — the channels S2 mints at — are absurd here because
  -- neither is in `ioES`, so only `input`/`output` survive and there `voteMints` is `[]`.
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
  -- every minted set.  THIS is why S2, like the other four, needs no copy→concrete
  -- transport.
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

  -- THE STATEMENT of S2 at the system level, over the CONCRETE per-link multiplexer
  VoteSoundLT : Set₁
  VoteSoundLT = VoteSpecT ⊑T leiosNet

  -- S2, PROVED OF THE WHOLE NETWORK.  `wf→osafe` turns the one `Wf fullα []` fact into
  -- an `OSafe []` fact — `noTick` coming from `noRet-system` over the per-node
  -- `noRet-logic` — and `osafe→⊑T` turns that into the refinement.
  voteSoundSys : VoteSoundLT
  voteSoundSys =
    osafe→⊑T (wf→osafe wf-system
                (noRet-system nodeBundleP NetworkLinkBreakableA _ noRet-logic))

------------------------------------------------------------------------
-- THE THEOREM, at the shared api alphabet
------------------------------------------------------------------------

-- S2 AT THE SYSTEM LEVEL, for every parameter set, every topology and every voter map:
-- no node of the whole N-node Leios-prototype network deposits a vote blob it cannot
-- vouch for at one of its OWN endpoints — either a neighbour delivered that exact blob
-- there, or the node itself read the ranking block the blob names AND the body of the EB
-- that block announces.  There is no premise at all — no oracle, no voter retraction and
-- no link configuration.  No validity is asserted: the prototype's votes carry no verdict.
voteSoundLT : ∀ (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
                (voterOf : Topology.Node t → Params.VoterId p)
            → Generic.VoteSoundLT p lp t (AA.apiES p) voterOf
voteSoundLT p lp t voterOf = Generic.voteSoundSys p lp t (AA.apiES p) voterOf

------------------------------------------------------------------------
-- The shipped Leios line
------------------------------------------------------------------------

open import Semantics.Failures
  {E = N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams)}
  {I = ExtI (N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams))} using (_⊑T_)

-- S2's discipline at the shipped three-node Linear-Leios line, where `VoterId = Node` and
-- the voter map is the identity
module VSLS = VS.Generic LIL.leiosLParams LIL.leiosLP LIL.leiosLLine
                         (AA.apiES LIL.leiosLParams) (λ n → n)

-- S2 AT THE SYSTEM LEVEL FOR THE SHIPPED LEIOS LINE, PREMISE-FREE, stated against the
-- shipped witness `LeiosInstanceL.leiosSystemL` itself: in the three-node line, every
-- node running the whole Linear-Leios logic from empty stores behind the twelve
-- prototype peers, over the concrete per-link multiplexer with io hidden, no node ever
-- deposits a vote blob unless a Notify votes delivery at one of its own endpoints carried
-- it, or it read both the ranking block the blob names and that block's announced EB body
-- out of its own stores.
leiosVoteSoundLT : VSLS.VoteSpecT ⊑T LIL.leiosSystemL
leiosVoteSoundLT =
  voteSoundLT LIL.leiosLParams LIL.leiosLP LIL.leiosLLine (λ n → n)

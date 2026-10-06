{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S4 AT THE SYSTEM LEVEL: CERTIFICATE-RB ORIGIN
-- OF THE WHOLE N-NODE LEIOS-PROTOTYPE NETWORK running `nodeLogicL` at every
-- node behind the prototype peer bundle `PeersP.nodeBundleP`, over the
-- CONCRETE per-link multiplexer `NetCommon.NetworkLinkBreakableA`, with the
-- io channels hidden.
--
-- WHAT IT SAYS.  No node of the network ever puts a certificate-carrying
-- ranking block into its own store unless THAT NODE'S own vote store had
-- certified the RB the certificate names, or a block certifying that RB
-- arrived off the wire AT ONE OF THAT NODE'S OWN ENDPOINTS.  "At that node"
-- is a fact about the discipline and not about the quantifier:
-- `CertRbOrigin`'s re-keying mints `((l , d) , r)` at
-- `store l d (stHasCert r)` — node-local, since `hasCertEv n r` fires at
-- `homeOf n` — and `(homeAt (l , d) , r)` at `apiBF l d recvBFBlock`, while a
-- `store l d stPut ! b` with `rbCert b = just r` demands `((l , d) , r)`.
-- `homeOf` is injective (`CertRbOrigin.homeOf-inj`), so a certificate or a
-- delivery at node X cannot open a gate at node Y even though both nodes'
-- api and store channels sit in the same composite.
--
-- DO NOT OVERSELL THIS ONE.  IT IS THE WEAKEST OF THE FIVE IN CONTENT, and
-- the lift does not change that.  S4's WIRE CLAUSE IS SELF-LICENSING BY
-- DESIGN (the forge-route scope recorded at `NodeLogicL.agda:264-273` and in
-- `CertRbOrigin`'s header): a delivery at one of a node's own endpoints mints
-- exactly the key the deposit that follows it demands, so the wire route is
-- UNCONSTRAINED at the system level just as it is at node level.  What the
-- endpoint key buys is only that node X's certificates and deliveries no
-- longer licence node Y's deposits — necessary for the network statement to
-- mean anything, NOT a new restriction on what a node may accept.  The
-- quotable form is "a cert-RB a node INVENTS was certified by that node";
-- never "every cert-RB in the network was earned somewhere".
--
-- WHAT IT DOES NOT SAY — `CertRbOrigin`'s deliberate gaps, unchanged by the
-- lift.  Nothing about whether the certificate is JUSTIFIED (that is S3's
-- business, and whether the blobs behind it were cast is S2/S2′'s).  Because
-- the wire clause mints a HASH and not a block, one delivery licenses the
-- deposit of every block carrying that same certificate hash at that node.
-- Nothing about the other four stores.  Nothing about a certificate-free
-- block, which the gate licenses outright.  Nothing about liveness — the
-- forge route's first step is exhibited at `NodeLogicLSanity`, but no module
-- exhibits a node reaching the deposit — and nothing about divergence: `⊑T`
-- is a safety order.
--
-- THE PREMISES.  NONE.  `CertRbOrigin.Generic` takes exactly the five
-- arguments `NodeLogicL.Generic` takes, all of them data about the parameter
-- set; there is no monotonicity premise (that is S3's), no voter retraction
-- (that is S2′'s) and no link-configuration premise: unlike S0, this theorem
-- needs no copy→concrete medium transport, so
-- `AnnounceSafeConcrete.LinkCfgWf` never arises.  `certRbSoundLT` below is
-- therefore unconditional at every parameter set, and `leiosCertRbSoundLT` is
-- the same statement at the shipped three-node line.
--
-- WHAT IS REUSED VERBATIM FROM `Leios.CertSystemL`, `Leios.BlobSystemL` and
-- `Leios.BodySystemL`, as the pilot promised: `sep-io`, `hideCov-full`,
-- `med-noNeed`, `wf-med`, `noRet-system`, and the proof TERMS of
-- `wf-nodeC`/`wf-system`/`certRbSoundSys`.  `hideKeep-io`'s nineteen clauses
-- are not free, because its type mentions `next` hence the instance's
-- `mints`; they are mechanical here too — `certRbMints` fires only on
-- `store _ _ (stHasCert _)` and `apiBF _ _ recvBFBlock`, neither of which is
-- in `ioES`, so the only non-absurd clauses are `input`/`output`, where the
-- catch-all reduces to `[]`.
--
-- THE ONE THING S4 NEEDED THAT S3 DID NOT, and S2′/S1 did: its wire mint is
-- at a per-endpoint `apiBF` channel, so the leaf must know that the receiving
-- endpoint belongs to the depositing node — `Topology.endpoints-sound`,
-- delivered to the leaf by `BlockProvenanceWfR.wf-⦀⁺∈`.  Its RENDEZVOUS mint
-- is node-local, so record η closes that half definitionally, exactly as S3's
-- store mint does.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.CertRbSystemL where

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
import Cardano_network.Parametric.Leios.CertRbOrigin as CRO
import Cardano_network.Parametric.Leios.LeiosInstanceL as LIL
open import Cardano_network.Base using (Dir)

-- the system level of S4, parametric in the same five arguments `CertRbOrigin.Generic`
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
  -- S4's discipline, which re-exports (`public`) the shared leaves — `fullα`, the
  -- vacuous leaf, `sep-api`, the prototype peer bundle — the carrier names it uses, and
  -- the four only a system fold needs, so the `Wf` folded below is the very one
  -- `certRbSound` is proved with and no second `BlockProvenance.Carrier` application
  -- arises
  open CRO.Generic p lp t apiES voterOf
    using ( Minted; CertRbKey; certRbCarries; certRbWA; certRbNext; certRbNext-⊆; certRbMints
          ; needs-store; CertRbSpecT; wf→osafe; osafe→⊑T; wf-logic; noRet-logic
          ; fullα; noNeed; wf-free; sep-api; wf-linkBundlesP
          ; Wf; wf-mono-G; Sep; wf-Par
          ; wf-⦀Fin⁺; HideCov; HideKeep; wf-Hide )

  ------------------------------------------------------------------------
  -- The three side conditions of the system fold
  --
  -- All three are `CertSystemL`'s, which that file's closing note promised would
  -- transfer unchanged.  Nothing below mentions `stPut`, `stHasCert` or
  -- `recvBFBlock`.
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
  -- known.  `store` and `apiBF` — the two channels S4 mints at — are absurd here because
  -- neither is in `ioES`, so only `input`/`output` survive and there `certRbMints` is
  -- `[]`.
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
  -- every minted set.  THIS is why S4, like S3, S2′ and S1, needs no copy→concrete
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

  -- THE STATEMENT of S4 at the system level, over the CONCRETE per-link multiplexer
  CertRbSoundLT : Set₁
  CertRbSoundLT = CertRbSpecT ⊑T leiosNet

  -- S4, PROVED OF THE WHOLE NETWORK.  `wf→osafe` turns the one `Wf fullα []` fact into
  -- an `OSafe []` fact — `noTick` coming from `noRet-system` over the per-node
  -- `noRet-logic` — and `osafe→⊑T` turns that into the refinement.
  certRbSoundSys : CertRbSoundLT
  certRbSoundSys =
    osafe→⊑T (wf→osafe wf-system
                (noRet-system nodeBundleP NetworkLinkBreakableA _ noRet-logic))

------------------------------------------------------------------------
-- THE THEOREM, at the shared api alphabet
------------------------------------------------------------------------

-- S4 AT THE SYSTEM LEVEL, for every parameter set, every topology and every voter map:
-- no node of the whole N-node Leios-prototype network puts a certificate-carrying ranking
-- block into its own store unless that node's own vote store certified the RB named, or a
-- block certifying it arrived at one of that node's OWN endpoints.  There is no premise at
-- all — no oracle, no voter retraction and no link configuration.  FORGE-ROUTE SCOPED and
-- the weakest of the five in content; see the module header before quoting it.
certRbSoundLT : ∀ (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
                (voterOf : Topology.Node t → Params.VoterId p)
            → Generic.CertRbSoundLT p lp t (AA.apiES p) voterOf
certRbSoundLT p lp t voterOf = Generic.certRbSoundSys p lp t (AA.apiES p) voterOf

------------------------------------------------------------------------
-- The shipped Leios line
------------------------------------------------------------------------

open import Semantics.Failures
  {E = N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams)}
  {I = ExtI (N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams))} using (_⊑T_)

-- S4's discipline at the shipped three-node Linear-Leios line, where `VoterId = Node` and
-- the voter map is the identity
module CRLS = CRO.Generic LIL.leiosLParams LIL.leiosLP LIL.leiosLLine
                         (AA.apiES LIL.leiosLParams) (λ n → n)

-- S4 AT THE SYSTEM LEVEL FOR THE SHIPPED LEIOS LINE, PREMISE-FREE, stated against the
-- shipped witness `LeiosInstanceL.leiosSystemL` itself: in the three-node line, every
-- node running the whole Linear-Leios logic from empty stores behind the twelve
-- prototype peers, over the concrete per-link multiplexer with io hidden, no node ever
-- puts a certificate-carrying ranking block into its own store unless that node's own
-- vote store had certified the RB named, or a block certifying it arrived at one of that
-- node's own endpoints.  FORGE-ROUTE SCOPED — the wire clause is self-licensing.
leiosCertRbSoundLT : CRLS.CertRbSpecT ⊑T LIL.leiosSystemL
leiosCertRbSoundLT =
  certRbSoundLT LIL.leiosLParams LIL.leiosLP LIL.leiosLLine (λ n → n)

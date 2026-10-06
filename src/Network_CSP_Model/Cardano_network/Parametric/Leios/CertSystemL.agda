{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S3 AT THE SYSTEM LEVEL: CERT SOUNDNESS OF THE
-- WHOLE N-NODE LEIOS-PROTOTYPE NETWORK running `nodeLogicL` at every node
-- behind the prototype peer bundle `PeersP.nodeBundleP`, over the CONCRETE
-- per-link multiplexer `NetCommon.NetworkLinkBreakableA`, with the io
-- channels hidden.
--
-- WHAT IT SAYS.  No node of the network ever issues a certificate for a
-- ranking-block hash that its OWN certification oracle does not grant on
-- the vote blobs deposited AT THAT NODE.  "At that node" is now a fact
-- about the discipline and not about the quantifier: `CertSound`'s
-- re-keying (commit "key the S3 origin discipline by the endpoint a vote
-- was deposited at") mints `((l , d) , v)` at `store l d stPutVote` and
-- demands `((l , d) , r)` at `store l d stCert`, so a deposit at node X
-- cannot open a gate at node Y even though both nodes' stores sit in the
-- same composite.
--
-- WHAT IT DOES NOT SAY.  Not a validity statement (the prototype's vote
-- blob carries NO verdict — `CertSound`'s header, rule 1).  Nothing about
-- liveness: no module exhibits a node actually reaching `stCert`.  Nothing
-- about divergence: `⊑T` is a safety order.  And nothing about WHO cast a
-- blob — that a blob really came from the voter it names is S2′.
--
-- THE PREMISE.  Exactly `CertSound`'s: a MONOTONE oracle
-- (`LeiosParams.CertifiesMono`), carried in `Assembly`'s telescope because
-- the specification itself is a module application that consumes it.  It is
-- DISCHARGED at the shipped line by `CertSound.certMonoL`, so
-- `leiosCertSoundLT` at the bottom is unconditional.  There is NO link
-- configuration premise: unlike S0, this theorem needs no copy→concrete
-- medium transport (see below), so `AnnounceSafeConcrete.LinkCfgWf` never
-- arises.
--
-- WHY THIS IS SO MUCH SMALLER THAN S0 (`Leios.AnnounceSystemL`, 466 lines).
-- S0's `Carries` fires on wire AND api channels, so it needs partial
-- guarantee alphabets, a nine-clause `sep-ioL`, an eighteen-clause
-- `sep-apiL` and a `Covers` enumeration.  EVERY origin discipline confines
-- `Carries` to a single `store` channel (`CertSound.needs-store`), and that
-- collapses the whole assembly:
--
--   * every alphabet is `OriginLeaves.fullα`, so every `Sep` is the
--     two-liner `(λ _ _ _ → tt) , (λ _ _ _ → tt)` — `sep-api` as shipped,
--     and `sep-io` below is the same shape at `ioES`;
--   * `HideCov ioES fullα` is `λ _ _ → tt`: no `Covers` enumeration;
--   * THE MEDIUM IS A SIX-LINE VACUITY, not a module.  `MediumEquivA`
--     classifies every `store` channel as belonging to no link, and
--     `oo-breakableNetLinkA` gives each CONCRETE cell its link alphabet, so
--     `wf-free` applies to the concrete multiplexer directly.  CONSEQUENCE:
--     no copy medium, no `systemN-monoWith-T` transport, no `LinkCfgWf`.
--     S0 could not do this because the medium really does carry blocks.
--
-- WHAT IS DISCIPLINE-PARAMETRIC HERE, i.e. what S1/S2/S2′ can take
-- verbatim once they are re-keyed: `sep-io`, `hideCov-full`,
-- `hideKeep-io`, `wf-med`, `med-noNeed`, `noRet-system`, and the shape of
-- `wf-nodeC`/`wf-system`/`certSoundSys`.  Of those, only `hideKeep-io`
-- mentions the instance at all, and only through the ONE fact that no io
-- channel mints.  See the note at the bottom of this file.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.CertSystemL where

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
import Cardano_network.Parametric.Leios.CertSound as CS
import Cardano_network.Parametric.Leios.LeiosInstanceL as LIL
open import Cardano_network.Base using (Dir)

-- the system level of S3, parametric in the same five arguments `CertSound.Generic`
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
  -- S3's discipline, at the SAME five parameters, so its `Minted`/`NeedKey` are the ones
  -- the two carrier opens below are instantiated at
  -- `CertSound.Generic` re-exports (`public`) both the shared leaves — `fullα`, the
  -- vacuous leaf, `sep-api`, the whole prototype peer bundle — and the carrier names it
  -- uses, so they come through HERE and the two `Wf`s are one record by construction.
  -- … including the four carrier names `CertSound` does not itself use, which it now
  -- re-exports, so `wf-Hide`/`wf-⦀Fin⁺` fold the very `Wf` opened here and no second
  -- application of `BlockProvenance.Carrier` is needed
  open CS.Generic p lp t apiES voterOf
    using ( Minted; NeedKey; certCarries; certWA; certNext; certNext-⊆; certMints
          ; needs-store; CertifiesMono
          ; fullα; noNeed; wf-free; sep-api; wf-linkBundlesP
          ; Wf; wf-mono-G; Sep; wf-Par
          ; wf-⦀Fin⁺; HideCov; HideKeep; wf-Hide )

  ------------------------------------------------------------------------
  -- The three side conditions of the system fold
  --
  -- All three are trivial, and all three are DISCIPLINE-PARAMETRIC: nothing below
  -- mentions `stCert`, `stPutVote` or the oracle.  They hold for S1/S2/S2′ unchanged.
  ------------------------------------------------------------------------

  -- SEP AT THE IO RENDEZVOUS: both the medium and the node fold carry the FULL
  -- guarantee alphabet, so there is nothing to reroute — the same two-liner as
  -- `OriginLeaves.sep-api`.  This is the whole saving over `AnnounceSystemL.sep-ioL`,
  -- which needs nine clauses because S0's alphabets are partial.
  sep-io : Sep ioES fullα fullα
  sep-io = (λ _ _ _ → tt) , (λ _ _ _ → tt)

  -- THE COVERAGE CONDITION OF HIDING: a hidden carrying label must be guaranteed by the
  -- process under the `∖`, and on the full alphabet every label is.  No `Covers`
  -- enumeration (`AnnounceSystemL.covers-sysGL`) is needed at all.
  hideCov-full : HideCov ioES fullα
  hideCov-full _ _ = tt

  -- NO IO CHANNEL MINTS, so hiding one leaves the minted set alone.  One clause per
  -- `Net_Api` constructor, because `ioSet` does not reduce until the constructor is
  -- known — the shape of `BlockProvenance.hideKeep-ioES`.  This is the ONE place the
  -- discipline shows through: it is `certMints`' catch-all that makes each clause go.
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
  -- node-local channel, in fact — to `nothing`.
  med-noNeed : ∀ at a → unionAlpha linkAlphaA at a → noNeed at a
  med-noNeed (X , e) a (i , k , q) c with needs-store {e = e} c
  ... | _ , _ , _ , refl = case q of λ ()

  -- THE CONCRETE PER-LINK MULTIPLEXER IS A VACUITY, at every guarantee alphabet and
  -- every minted set.  `⦀Fin` unions the per-cell alphabets `oo-breakableNetLinkA`
  -- supplies, and `med-noNeed` sends that union into the "carries nothing" confinement
  -- `OriginLeaves.wf-free` consumes.  THIS is why S3 needs no copy→concrete transport.
  wf-med : ∀ {ms} → Wf fullα ms NetworkLinkBreakableA
  wf-med = wf-free (OffersOnly-mono med-noNeed (OffersOnly-⦀Fin oo-breakableNetLinkA))

  ------------------------------------------------------------------------
  -- `noTick`
  ------------------------------------------------------------------------

  -- THE WHOLE NETWORK NEVER RETURNS, over ANY medium and ANY peer-bundle builder: hide,
  -- medium-right, node fold head, logic-right.  Nothing here inspects the builder — only
  -- the shape `nodeWith mk n lg = linkBundlesWith mk n ∥⇘ apiES ⇙ lg`, which holds for
  -- every `mk`.  Verbatim `AnnounceSystemL.noRet-systemL`, re-derived here rather than
  -- imported so that S3 pulls in none of the announcement campaign.
  noRet-system : ∀ (mk : Link → Dir → Dir → Proc) med (lg : Node → Proc)
               → (∀ n → NoRet (lg n)) → NoRet (systemOfWithNode (nodeWith mk) med lg)
  noRet-system mk med lg h =
    NoRet-Hide ioES
      (NoRet-ParR ioES (NoRet-⦀Fin⁺ numNodes-1 (NoRet-ParR apiES (h fzero))))

  ------------------------------------------------------------------------
  -- The statement, and the assembly under the one premise
  ------------------------------------------------------------------------

  -- THE SHIPPED NETWORK: the N-node Leios-prototype system this file is about, named so
  -- the headline can quote it without re-opening `Node`
  leiosNet : Proc
  leiosNet =
    systemOfWithNode (nodeWith nodeBundleP) NetworkLinkBreakableA (λ n → nodeLogicL n st₀)

  -- the module S3's monotonicity premise buys: the specification and the theorem
  module Assembly (certMono : CertifiesMono) where

    -- S3's proof module at this oracle — the SAME one `certSound` is proved in, so the
    -- specification below is literally the node-level theorem's
    open CS.Generic.Sound p lp t apiES voterOf certMono
      using (CertSpecT; wf→osafe; osafe→⊑T; wf-logic; noRet-logic; nodeP)

    -- ONE LEIOS NODE on the full alphabet: the twelve prototype peers against the
    -- Linear-Leios logic, `sep-api` discharging the api rendezvous because both sides
    -- carry the full alphabet
    wf-nodeC : ∀ {ms} n → Wf fullα ms (nodeP n (nodeLogicL n st₀))
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

    -- THE STATEMENT of S3 at the system level, over the CONCRETE per-link multiplexer
    CertSoundLT : Set₁
    CertSoundLT = CertSpecT ⊑T leiosNet

    -- S3, PROVED (under `CertifiesMono`) OF THE WHOLE NETWORK.  `wf→osafe` turns the one
    -- `Wf fullα []` fact into an `OSafe []` fact — `noTick` coming from `noRet-system`
    -- over the per-node `noRet-logic` — and `osafe→⊑T` turns that into the refinement.
    certSoundSys : CertSoundLT
    certSoundSys =
      osafe→⊑T (wf→osafe wf-system
                  (noRet-system nodeBundleP NetworkLinkBreakableA _ noRet-logic))

------------------------------------------------------------------------
-- THE THEOREM, at the shared api alphabet
------------------------------------------------------------------------

-- S3 AT THE SYSTEM LEVEL, for every parameter set, every monotone Leios oracle, every
-- topology and every voter map: no node of the whole N-node Leios-prototype network
-- issues a certificate its own oracle does not grant on the vote blobs deposited at
-- THAT node.  The only premise is `CertifiesMono`; there is no link-configuration
-- premise, because the concrete medium is `Wf` directly.
certSoundLT : ∀ (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
                (voterOf : Topology.Node t → Params.VoterId p)
            → (certMono : LeiosP.CertifiesMono p lp)
            → Generic.Assembly.CertSoundLT p lp t (AA.apiES p) voterOf certMono
certSoundLT p lp t voterOf certMono =
  Generic.Assembly.certSoundSys p lp t (AA.apiES p) voterOf certMono

------------------------------------------------------------------------
-- The shipped Leios line: premise-free
------------------------------------------------------------------------

open import Semantics.Failures
  {E = N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams)}
  {I = ExtI (N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams))} using (_⊑T_)

-- S3 AT THE SYSTEM LEVEL FOR THE SHIPPED LEIOS LINE, PREMISE-FREE, stated against the
-- shipped witness `LeiosInstanceL.leiosSystemL` itself: in the three-node line, every
-- node running the whole Linear-Leios logic from empty stores behind the twelve
-- prototype peers, over the concrete per-link multiplexer with io hidden, no node ever
-- issues a certificate for a ranking block that the line's own oracle does not grant on
-- the vote blobs deposited at that node.  The premise is discharged by
-- `CertSound.certMonoL` — `leiosLP` certifies `r` exactly when SOME blob held names
-- `r`, and `any` is `⊆`-monotone.
leiosCertSoundLT : CS.CSLS.CertSpecT ⊑T LIL.leiosSystemL
leiosCertSoundLT =
  certSoundLT LIL.leiosLParams LIL.leiosLP LIL.leiosLLine (λ n → n) CS.certMonoL

------------------------------------------------------------------------
-- WHAT S1/S2/S2′/S4 INHERITED FROM THIS FILE
--
-- Everything above `Assembly` is discipline-parametric, and the four later lifts
-- (`BodySystemL`, `VoteSystemL`, `BlobSystemL`, `CertRbSystemL`) took it with NO
-- change once each discipline had been re-keyed by endpoint the way `CertSound` was:
--
--   * `sep-io`, `hideCov-full` — they mention only `fullα`, which every origin
--     discipline's leaves live on;
--   * `med-noNeed`, `wf-med` — they spend only `needs-store`, which every discipline has
--     to write anyway to state its own gate.  Each instance supplied its own
--     `needs-store` and got the medium for two lines;
--   * `noRet-system` — pure `NoRet`, mentions no `Carries` and no builder;
--   * `wf-nodeC`, `wf-system`, `certSoundSys` — their proof TERMS are identical; only
--     the per-instance `wf-logic`/`noRet-logic` they are applied to differ.
--
-- The ONE thing that was not free is `hideKeep-io`'s nineteen clauses: its type mentions
-- `next`, hence the instance's `mints`.  It is mechanical (the only non-absurd clauses
-- are `input`/`output`, where the catch-all of `mints` reduces) and identical in shape
-- for all five, so each of the five origin system modules now carries its own copy.
-- Hoisting it into `OriginLeaves.Leaves` would cost ONE premise — "`mints` is empty on
-- `input` and `output`" — and is now a LIVE question rather than a deferred one: the
-- abstraction would have five consumers, not the one that made it an anti-pattern when
-- this file was the pilot.  It is still NOT taken here, and it is not a local edit if
-- taken: it would rewrite all five green system modules at once, each needing a
-- re-check.  (S0's `AnnounceSystemL` is not a consumer — it spends
-- `BlockProvenance.hideKeep-ioES` directly.)
------------------------------------------------------------------------

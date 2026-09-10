{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE REACHABILITY WITNESS for the Leios
-- announcement.
--
-- WHY THIS MODULE EXISTS.  Every module above `Parametric.NodeLogic`
-- typechecks green whether or not the relay logic can actually MOVE: a
-- thread that names api events no peer ever offers blocks on its first
-- event forever, and every downstream statement about announcements
-- stays true, vacuously.  That is exactly the state the development was
-- in until 2026-09-07, when two defects were fixed in `NodeLogic`:
--
--   (A) `serverLoop`/`lnServerLoop` drove the endpoint's OWN direction
--       `d`, while `Node.bundleAt (l , d) = nodeBundle l d (opposite
--       d)` puts the node's server peers at `opposite d`;
--   (B) nothing anywhere drove the LeiosNotify CLIENT, so no
--       `MsgLNRequestNext` was ever emitted, so no LN server peer ever
--       left `stIdle`, so `sendLNBlockAnnouncement` — the event the
--       whole announcement-safety campaign is about — was not reachable
--       at all.
--
-- A green typecheck cannot tell those two states apart.  This module
-- can: it exhibits a MACHINE-CHECKED TRACE that ends in the announce
-- event, so the property `AnnounceSafe`/`AnnounceInvariant` constrain is
-- demonstrably non-empty.
--
-- WHICH LEVEL.  The witness is over ONE NODE — `node n (nodeLogic n
-- held)`, i.e. a node's full link bundle synchronised on `apiES` with
-- its full relay logic and block store — not over the whole `systemOf`
-- composite.  It therefore demonstrates the direction fix (A) and the
-- LN-server half of (B) end to end, and it is honest about what it does
-- NOT show: the `MsgLNRequestNext` that opens the round is supplied here
-- as a free `output … N2N_LeiosNotify` event, because at a single node
-- the medium is absent and `output ∉ apiES`.  In the full network that
-- same event comes out of the medium, driven by the FAR node's
-- `lnClientLoop` (fix (B)'s other half).  See the note on
-- `announce-fires` for why the full-composite version is out of reach
-- at this `Params`.
--
-- THE SCENARIO.  Node 0 of `LeiosInstance`'s three-node Leios line: a
-- degree-1 node whose only endpoint is `(link 0 , lo)`, so its bundle is
-- `nodeBundle 0 lo hi` — the ten peers `leiosCfg` configures, KA/CS/BF/TS/LN
-- in both directions — and its server peers sit at `hi`.  (Before this module
-- switched to the config-driven builder the bundle was `miniProtocols 0 lo hi`,
-- twelve peers; the two agree up to `∼` on a fully-configured link, see
-- `Cardano_network.BundleBridge`, and the ten-peer prefix the four steps below
-- traverse is component-for-component identical.)  Its store
-- starts holding one ranking block, `just true`, which announces the EB
-- whose hash is `true` (both branches of the announcement gate are
-- reachable at `leiosParams` — that is what `LeiosInstance` is for).
--
-- PROOF TECHNIQUE.  The four steps are assembled from the parallel
-- transition INTRO lemmas of `CSP.Laws.Traces.TraceLawsParallel`
-- (`Par-sync`, `Par-soloL`, `Par-soloR`, `Par-τ-L`, `Par-τ-R`), so the
-- only hand-written LTS constructors are the four leaf steps inside the
-- peer, the thread and the store.  Every `refl` below is a computation:
-- `loop`/`iter`/`>>=`/`pchoice`/`renameMap`/`Par` are all plain
-- non-abstract functions, so Agda reduces the composite's offer maps on
-- its own (the same idiom as `Parametric.AnnounceContent`).
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.RelayLive where

open import Level using (0ℓ)
import Data.Unit.Polymorphic as Poly
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees using (ExtI)

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.LeiosInstance
  using (leiosParams; leiosLine)
open import CSP.Examples.Cardano_network.Base
  using (lo; hi; N2N_LeiosNotify; FromInitiator)
open import CSP.Examples.Cardano_network.Net leiosParams
  using ( Net_Api; Net_Api-≟; output; store; apiLN
        ; stGet; sendLNBlockAnnouncement )
open import CSP.Examples.Cardano_network.Data leiosParams
  using (Payload; Header; header; Messages; leiosNotify; MsgLNRequestNext)
open import CSP.Examples.Cardano_network.ApiAlphabet leiosParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node leiosParams leiosLine apiES
  using (Proc; node)
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
open NL.Generic leiosParams leiosLine apiES using (Held; nodeLogic)

open Params leiosParams using (Block)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R)

------------------------------------------------------------------------
-- The scenario
------------------------------------------------------------------------

-- the node under test: node 0 of the Leios line, degree 1, its only endpoint
-- being `(link 0 , lo)` — so its server peers, and hence its announcements, sit
-- at direction `hi`
nA : Fin 3
nA = fzero

-- the ranking block node 0's store starts with: it announces the EB whose hash is
-- `true` (`leiosParams.announcedEB = λ b → b`, `Block = Maybe Bool`)
blk : Block
blk = just true

-- node 0's initial store contents: the one block above
held₀ : Held
held₀ = blk ∷ []

-- THE PROCESS UNDER TEST: node 0's whole link bundle synchronised on `apiES` with
-- its whole relay logic (mint, the four endpoint threads, the block store)
relayNode : Proc
relayNode = node nA (nodeLogic nA held₀)

------------------------------------------------------------------------
-- The three visible events of the witness trace
------------------------------------------------------------------------

-- the LeiosNotify request as it arrives off the wire at direction `hi`: this is what
-- the FAR node's `lnClientLoop` puts on the medium, and it is the ONLY thing that
-- moves an LN server peer out of `stIdle`
reqMsg : Payload
reqMsg = tt , FromInitiator , tt , leiosNotify MsgLNRequestNext

-- event 1: the request reaching node 0's LN server peer
evReq : Event√ (Poly.⊤ {0ℓ})
evReq = evl (evLabel Payload (output fzero hi N2N_LeiosNotify) reqMsg)

-- event 2: the announce thread taking the held block out of node 0's store
evGet : Event√ (Poly.⊤ {0ℓ})
evGet = evl (evLabel Block (store fzero lo stGet) blk)

-- event 3: THE ANNOUNCEMENT — the whole point of the witness
evAnn : Event√ (Poly.⊤ {0ℓ})
evAnn = evl (evLabel Header (apiLN fzero hi sendLNBlockAnnouncement) (header blk))

------------------------------------------------------------------------
-- The four steps
--
-- Each is stated as "there is a state such that …", so the target of one
-- step is `proj₁` of it and the next step's source; nothing large has to
-- be written out by hand.
------------------------------------------------------------------------

-- STEP 1.  The request arrives.  `output ∉ apiES`, so the bundle takes it alone
-- (`Par-soloL`); inside the bundle only the LN server peer at `hi` offers it, so it
-- rides past the nine peers before it and the two after it.
step₁ : Σ[ P₁ ∈ Proc ] (relayNode ─[ ev evReq ]─► P₁)
step₁ = _ ,
  Par-soloL _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      refl) refl) refl) refl) refl) refl) refl) refl) refl)
    refl

-- STEP 2.  The LN server peer's loop-back: having consumed the request it returns
-- `stBusy` to `iter`, whose `sil` guard is one τ.  This is the ONLY silent step the
-- witness needs.
step₂ : Σ[ P₂ ∈ Proc ] (proj₁ step₁ ─[ τ ]─► P₂)
step₂ = _ ,
  Par-τ-L _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-R _ _ _ _
    (Par-τ-L _ _ _ _ (sSil refl)))))))))))

-- STEP 3.  The announce thread takes the held block out of the store.  `store ∉
-- apiES` so the bundle stays put (`Par-soloR`), while inside the logic the event IS
-- in `storeES`, so the thread group and the block store synchronise on it.
step₃ : Σ[ P₃ ∈ Proc ] (proj₁ step₂ ─[ ev evGet ]─► P₃)
step₃ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
        refl) refl) refl)
      (sVis refl refl))
    refl

-- STEP 4.  THE ANNOUNCEMENT.  `apiLN ∈ apiES`, so this is a genuine rendezvous
-- between the LN server PEER (now in `stBusy`, thanks to step 1) and the node's
-- `lnServerLoop` THREAD (now holding the block, thanks to step 3).  Before the two
-- fixes of 2026-09-07 neither side could ever reach this state.
step₄ : Σ[ P₄ ∈ Proc ] (proj₁ step₃ ─[ ev evAnn ]─► P₄)
step₄ = _ ,
  Par-sync _ _ _ _ _
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ())
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)
      refl) refl) refl) refl) refl) refl) refl) refl) refl)
    (Par-soloL _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
        refl) refl) refl)
      refl)

------------------------------------------------------------------------
-- THE WITNESS
------------------------------------------------------------------------

-- THE ANNOUNCE EVENT IS REACHABLE.  Some state of node 0 of the concrete Leios line
-- is reached by a trace whose LAST event is `apiLN 0 hi sendLNBlockAnnouncement !
-- header (just true)`, so `AnnounceSafe`/`AnnounceInvariant` are not vacuous.
--
-- LEVEL 2 of the acceptance ladder, not level 1: over `node n (nodeLogic n held)`,
-- not over `systemOf`.
--
-- The ORIGINAL obstruction to level 1 has since been REMOVED.  It was
-- `LeiosInstance.leiosCfg`, which configured only the four Praos wire protocols, so
-- the medium had no `N2N_LeiosNotify` cell and could not carry `MsgLNRequestNext`
-- between nodes at all; `leiosCfg` now carries LN on both directions, and step 1
-- below is exactly the event that medium cell emits.
--
-- What remains is COST, not possibility.  A level-1 witness must drive the whole
-- `(medium ∥⇘ ioES ⇙ ⦀Fin⁺ 2 nodes) ∖ ioES` composite through the far node's LN
-- client, across two medium cells (`input`/`output`, both hidden by `∖ ioES` and so
-- reached by τ), and into this node's LN server — many more steps, each normalising
-- a strictly larger term than the four below.  This module already needs
-- `+RTS -M22G` and exhausts a 12G heap; a level-1 witness should be budgeted and
-- staged rather than attempted as an afterthought.  It is NOT built here, and
-- nothing below should be read as claiming it.
announce-fires : traces relayNode (evReq ∷ evGet ∷ evAnn ∷ [])
announce-fires =
  _ , ⟹-ev (proj₂ step₁)
      (⟹-τ (proj₂ step₂)
      (⟹-ev (proj₂ step₃)
      (⟹-ev (proj₂ step₄) ⟹-refl)))

-- NEGATIVE CONTROL: the announcement is not simply always on offer.  In the initial
-- state the LN server peer is in `stIdle`, where `serverStep`'s menu answers `nothing`
-- to every `apiLNev`, so no announcement is available until a request has arrived —
-- which is precisely why `lnClientLoop` (fix (B)) has to exist.  Only `sVis` can carry
-- an `ev` label out of a `react`-headed state, so one clause suffices.
announce-blocked-initially : ∀ {P′} → ¬ (relayNode ─[ ev evAnn ]─► P′)
announce-blocked-initially (sVis refl ())

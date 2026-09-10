{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — LINEAR LEIOS ANNOUNCEMENT SAFETY, stated
-- and reduced to per-node obligations.
--
-- THE PROPERTY.  A node may only announce (over LeiosNotify) a ranking
-- block whose announced EB hash was actually minted: performing
-- `apiLN l d sendLNBlockAnnouncement ! h` with `announcedEBof h ≡ just
-- eh` requires an earlier `env l′ d′ envMint ! (just e , b)` with
-- `ebHash e ≡ eh`.  An RB announcing no EB (`announcedEBof h ≡
-- nothing`) is unconstrained.
--
-- WHY IT IS TRUE.  NOT because a node's own mint guard makes its store
-- well-announced — it does not: `NodeLogic.storeStep`'s `putEv` clause
-- deposits a client-received block into the store with NO announcement
-- check, only `acceptMint` is guarded.  What actually holds is a
-- NETWORK-WIDE fact: `AnnounceSpec`'s `Minted` state is global —
-- `announceOffer` matches `env _ _ envMint` on every link and
-- direction, and `env` survives `∖ ioES` (`NetCommon.agda:122`) — so a
-- block that entered a store via `putEv` still has its provenance
-- chained, through the medium, back to SOME node's guarded mint, just
-- not necessarily this node's.  `lnServerLoop` announces only held RBs
-- (it reads one via `getEv n`).  Discharging that network-wide argument
-- is the per-node obligation this module leaves OPEN — it is the `hN`
-- premise of `announceSafe-from-nodes` below.
--
-- CONSEQUENCE FOR `nSpec` (the per-node spec argument of
-- `announceSafe-from-nodes` below): because the true reason is
-- network-wide, `nSpec n` CANNOT be a node-local "well-announced store"
-- invariant.  Taken in isolation, `node n (nodeLogic n [])` can `put !
-- b` for a `b` announcing a never-minted hash, then `get ! b`, then
-- announce it — a node-local gate makes `hN` unprovable, while a gate
-- loose enough to admit put-deposited blocks pushes the work into the
-- `res` residual instead.  That tension is what any successor plan
-- discharging `hN` has to price.
--
-- WHY `⊑F` AND NOT `⊑FD`.  At `⊑F` the assembly lemma is
-- `Assembly.Generic.systemN-mono-F`, whose hiding step uses the
-- UNCONDITIONAL `Hide-mono-⊑F`; the `⊑FD` route would drag in the
-- (unbuilt, reachability-closed) divergence-freedom premise of
-- `Hide-mono-⊑FD-df` for no gain.
--
-- CORRECTION (2026-09-07).  An earlier version of this header claimed
-- "`⊑T` is NOT an option: no `Hide-mono-⊑T` / `∥-mono-⊑T` /
-- `⦀Fin⁺-mono-⊑T` exists in `src/`".  That is FALSE at face value: the
-- repo spells the ORDER `_⊑T_` but names the LEMMAS with a superscript
-- `ᵀ`, so a grep for `⊑T` misses them.  Both
-- `Hide-mono-⊑ᵀ` (`CSP/Laws/Traces/TraceLawsHide.agda:314`) and
-- `Par-mono-⊑ᵀ` (`CSP/Laws/Traces/TraceLawsParallelMono.agda`)
-- exist and are UNCONDITIONAL.  The CSP-sugar corollaries
-- `∥-mono-⊑T` / `⦀Fin⁺-mono-⊑ᵀ` were absent when this note was first
-- written; they were added in `ef7e9d26` (same module) and this file
-- now DEPENDS on them via `Assembly.Generic.systemN-mono-T`.
--
-- SECOND CORRECTION (2026-09-08).  The note above went on to say that
-- `⊑F` is the WRONG ORDER FOR SAFETY, because `failures`
-- (`Semantics/Failures.agda`) ranges over STABLE residuals only, so an
-- implementation that makes a forbidden announcement and then diverges
-- would satisfy the property VACUOUSLY, and that `⊑T` "does not follow
-- from `⊑F` (no lemma anywhere in `src/` relates the two orders)".
--
-- That diagnosis was RIGHT and the defect was in `_⊑F_` itself, not in
-- this file.  `Semantics.Failures._⊑F_` compared FAILURES ONLY, whereas
-- Roscoe's stable-failures model 𝓕 represents a process as the PAIR
-- (traces, failures); FDR 4.2.7 rejects `assert STOP [F= (a -> DIV)`
-- with a TRACE counterexample.  `_⊑F_` is now that pair, so:
--
--   * `⊑T` DOES follow from `⊑F` — it is `proj₁` (`⊑F→⊑T`), and the
--     divergence-vacuity above is closed at `⊑F` too;
--   * the surviving refutation is about the FAILURES HALF `_⊇F_`
--     alone (`CSP.Examples.RefinementOrderCounterexamples`);
--   * `AnnounceSafeWith` below is therefore now STRICTLY STRONGER than
--     it was, and it implies `AnnounceSafeTWith` modulo the difference
--     between the two spec shapes (`AnnounceSpec` carries the `⊓ Stop`,
--     `AnnounceSpecT` does not).
--
-- The `⊑T` family (`AnnounceSpecT` / `AnnounceSafeTWith` /
-- `AnnounceSafeT` / `announceSafeT-from-nodes`) is KEPT: it states the
-- safety property at the order safety belongs at, over the leaner
-- Chaos-free spec, and is what `AnnounceContent` pins.
-- `CSP.Examples.Cardano_network.Parametric.AnnounceContent` is the
-- machine-checked negative control pinning `AnnounceSpecT`'s content.
--
-- THE SPEC SHAPE, AND WHY IT IS CHAOS- AND NOT RUN-SHAPED.  `AnnounceSpec`
-- is a stateful `loop` over the set of EB hashes minted so far, whose body
-- is `pchoice … ⊓ Stop`.  The `pchoice` is a pure-visible `react` node
-- offering EVERY event of EVERY channel, with exactly two channels treated
-- specially (mint grows the state, announce is gated by it).  It is
-- deliberately NOT a `□` of prefixes like `NodeLogic.blockStore`: a `□` can
-- only offer the finitely many channels it names, whereas a spec above the
-- whole network must permit every other event of the (open-ended,
-- link-indexed) alphabet freely, which is what `pchoice`'s arbitrary offer
-- map expresses.
--
-- The `⊓ Stop` is ESSENTIAL, and its absence was a real defect in an
-- earlier draft.  `pchoice` alone has `∅t`, so every state is STABLE, and
-- `Refuses` (`Semantics/Refusals.agda:25`) then lets the spec refuse only
-- subsets of the events it does not offer.  A `pchoice`-only spec therefore
-- refuses almost nothing, and `⊑F` (which requires
-- `failures Q s X → failures P s X`) would force the IMPLEMENTATION to
-- offer, in every stable reachable state, every event on every link — which
-- it cannot: `NodeLogic.mint` offers `env` on ONE link only, and the six
-- un-driven Leios carriers are never offered at all.  That reading is FALSE
-- where a stable state is reachable and vacuous otherwise.  A SAFETY
-- property in the failures model must be able to refuse ARBITRARY sets, so
-- that it constrains traces only: `⊓ Stop` lets the spec always internally
-- decide to refuse everything.  `Stop` contributes no traces, so the
-- announcement gate keeps its full content.
--
-- WHICH FAMILY TO DISCHARGE (2026-09-09).  The `⊑T` one: the two
-- families now COLLAPSE.  `announceSpec-saturated` proves the `⊓ Stop`
-- makes `AnnounceSpec` refusal-saturated, `announceSpecT-traces⊆` proves
-- the `⊓ Stop` adds no traces, and `announceSafeT→announceSafe` spends
-- both — so a discharged `AnnounceSafeTWith` yields `AnnounceSafeWith`
-- at the same medium for free.  Nothing has to be proved twice.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceSafe where

open import Level using (0ℓ; Lift; lift)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit.Polymorphic using (⊤)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ContinueType; ExtI; NodeKind; react; base; pair; fin)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.Assembly as Asm

------------------------------------------------------------------------
-- The generic layer
------------------------------------------------------------------------

-- announcement safety, parametric in the network parameters, the topology and the
-- api alphabet — the same three parameters `Parametric.Node`, `Parametric.NodeLogic`
-- and `Parametric.Assembly` take, so `node`/`systemOfWith`/`nodeLogic` below are
-- literally those modules'
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (EB; EBHash; ebHash; decEBHash)
  open N p
    using ( Net_Api; Net_Api-≟; env; apiLN; envMint; sendLNBlockAnnouncement
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLF; store; break
          ; sendLNRequestNext; sendLNDone; sendLNBlockOffer; sendLNBlockTxsOffer
          ; sendLNVotesOffer; recvLNBlockAnnouncement; recvLNBlockOffer
          ; recvLNBlockTxsOffer; recvLNVotesOffer )
  open D p using (Payload; Header; announcedEBof)
  open Topology t using (Node; numNodes-1)
  open import CSP.Examples.Cardano_network.NetCommon p
    using (NetworkLinkBreakableA; ioES)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (_∥⇘_⇙_; _∖_; ⦀Fin⁺; _⊓_; Stop; pchoice; loop; Ret; _>>=_; iter; iter-bind; ∅t; bindV; bindT)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES
    using (Proc; node; systemOfWith)
  open NL.Generic p t apiES using (nodeLogic)
  open import Semantics.LTS
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Event√; ev; τ; _─[_]─►_; sRet; sSil; sVis; sTau)
  open import Semantics.Refusals
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Refuses)
  open import Semantics.Failures
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (_⊑F_; ⊑F-trans; _⊑T_; ⊑T-trans; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
  open import Semantics.RefinementOrders
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Saturated; saturated→⊑T→⊑F)
  open import CSP.Laws.Bisim.IterCong (Net_Api-≟ {Payload})
    using (iterV-elim; iterV-eq)
  open import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload})
    using (bindV-elim; bindV-eq)

  ------------------------------------------------------------------------
  -- The specification
  ------------------------------------------------------------------------

  -- the spec's state: the EB hashes the environment has minted so far.  Hashes are
  -- never removed — the permission an announcement needs, once granted, is permanent.
  Minted : Set
  Minted = List EBHash

  -- has this EB hash been minted?
  mintedIn : EBHash → Minted → Bool
  mintedIn eh ms = any (λ x → ⌊ x ≟ eh ⌋) ms

  -- may header `h` be announced against the minted set `ms`?  An RB announcing no EB
  -- is unconstrained; one announcing `eh` needs `eh` minted.
  announceOK : Minted → Header → Bool
  announceOK ms h with announcedEBof h
  ... | nothing = true
  ... | just eh = mintedIn eh ms

  -- the spec's offer map: mint grows the state, a gated announce keeps it, every
  -- other event of every other channel is offered freely and leaves the state alone
  announceOffer : Minted → (at : AnyTypes (Net_Api Payload))
                → ContinueType at
                    (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Minted))
  announceOffer ms (_ , env _ _ envMint) (just e  , _) = just (Ret (ebHash e ∷ ms))
  announceOffer ms (_ , env _ _ envMint) (nothing , _) = just (Ret ms)
  announceOffer ms (_ , apiLN _ _ sendLNBlockAnnouncement) h =
    if announceOK ms h then just (Ret ms) else nothing
  announceOffer ms _ _ = just (Ret ms)

  -- ANNOUNCEMENT SAFETY AS A PROCESS: every TRACE is permitted except one announcing
  -- an EB hash no mint produced.  Started from the empty minted set.  The `⊓ Stop`
  -- makes it Chaos-shaped rather than RUN-shaped, so it imposes no offer obligation
  -- on the implementation — see the header.
  AnnounceSpec : Proc
  AnnounceSpec = loop (λ ms → pchoice (announceOffer ms) ⊓ Stop) []

  -- announcement safety of the whole N-node relay network over an ARBITRARY medium,
  -- every store initially empty, at STABLE-FAILURES refinement.
  --
  -- PREFER `AnnounceSafeTWith` BELOW — but note the reason has changed.  Since
  -- 2026-09-08 `_⊑F_` is Roscoe's PAIR (traces, failures), so `⊑T` DOES follow
  -- from `⊑F` (`Semantics.Failures.⊑F→⊑T`) and this form is no longer the weaker
  -- statement it was.  It is retained because it is already referenced and
  -- because it is stated over the Chaos-shaped `AnnounceSpec`; the historic
  -- warning that followed applies to the FAILURES HALF `_⊇F_` only: `⊇F`
  -- compares STABLE failures only, so an implementation that announces an unminted
  -- hash and then diverges satisfies this VACUOUSLY.  The `⊑T` family below closes
  -- that hole, and `Parametric.AnnounceContent` machine-checks that it has content.
  --
  -- This is a `Set₁`, not `Set`: `_⊑F_` lands in `lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr`, which
  -- is `Level.suc 0ℓ` here.  Nothing in the property mentions the medium beyond the
  -- composition itself, so it reads the same at either.
  AnnounceSafeWith : Proc → Set₁
  AnnounceSafeWith med = AnnounceSpec ⊑F systemOfWith med (λ n → nodeLogic n [])

  -- announcement safety at the DEFAULT medium: the concrete per-link multiplexer,
  -- i.e. exactly `Parametric.Node.systemOf`
  AnnounceSafe : Set₁
  AnnounceSafe = AnnounceSafeWith NetworkLinkBreakableA

  -- ANNOUNCEMENT SAFETY AS A PROCESS, at TRACE refinement: every trace is permitted
  -- except one announcing an EB hash no mint produced.  No `⊓ Stop` here — `⊑T`
  -- ignores refusals entirely, so the Chaos-shaping the `⊑F` statement needs is inert.
  AnnounceSpecT : Proc
  AnnounceSpecT = loop (λ ms → pchoice (announceOffer ms)) []

  -- announcement safety over an arbitrary medium, at `⊑T` — the order safety actually
  -- belongs in: unlike `AnnounceSafeWith`, a run with no stable residual (a divergent
  -- implementation that first announces an unminted hash) cannot satisfy this vacuously.
  AnnounceSafeTWith : Proc → Set₁
  AnnounceSafeTWith med = AnnounceSpecT ⊑T systemOfWith med (λ n → nodeLogic n [])

  -- announcement safety at `⊑T`, at the DEFAULT medium (the concrete per-link
  -- multiplexer), i.e. exactly `Parametric.Node.systemOf`
  AnnounceSafeT : Set₁
  AnnounceSafeT = AnnounceSafeTWith NetworkLinkBreakableA

  ------------------------------------------------------------------------
  -- The reduction
  ------------------------------------------------------------------------

  -- announcement safety follows from one `⊑F` obligation per node plus one for the
  -- medium `med`, plus the residual goal that the abstracted composite itself is
  -- safe: `systemN-mono-F` folds them with no alphabet side conditions and no
  -- divergence premise.  The medium is an explicit argument, in the same style as
  -- `Assembly.Generic.systemN-mono`, so the reduction is usable at the concrete
  -- multiplexer (giving `AnnounceSafe`) and at the abstract copy medium alike.
  announceSafe-from-nodes :
      (med : Proc) (mSpec : Proc) (nSpec : Node → Proc)
    → mSpec ⊑F med
    → (∀ n → nSpec n ⊑F node n (nodeLogic n []))
    → AnnounceSpec ⊑F ((mSpec ∥⇘ ioES ⇙ ⦀Fin⁺ numNodes-1 nSpec) ∖ ioES)
    → AnnounceSafeWith med
  announceSafe-from-nodes med mSpec nSpec hM hN res =
    ⊑F-trans res (Asm.Generic.systemN-mono-F p t apiES med mSpec nSpec _ hM hN)

  -- the `⊑T` reduction: one obligation per node plus one for the medium, plus the
  -- residual.  Like its `⊑F` sibling this uses only unconditional laws —
  -- `systemN-mono-T` is `Hide-mono-⊑ᵀ` over `∥-mono-⊑T`/`⦀Fin⁺-mono-⊑ᵀ`, none of
  -- which carry an alphabet side condition or a divergence premise.
  announceSafeT-from-nodes :
      (med : Proc) (mSpec : Proc) (nSpec : Node → Proc)
    → mSpec ⊑T med
    → (∀ n → nSpec n ⊑T node n (nodeLogic n []))
    → AnnounceSpecT ⊑T ((mSpec ∥⇘ ioES ⇙ ⦀Fin⁺ numNodes-1 nSpec) ∖ ioES)
    → AnnounceSafeTWith med
  announceSafeT-from-nodes med mSpec nSpec hM hN res =
    ⊑T-trans res (Asm.Generic.systemN-mono-T p t apiES med mSpec nSpec _ hM hN)

  ------------------------------------------------------------------------
  -- THE COLLAPSE: the `⊑T` family delivers the `⊑F` one
  --
  -- `AnnounceSpec`'s `⊓ Stop` makes it REFUSAL-SATURATED: from every state
  -- it reaches, one τ enters the `Stop` branch, which is stable and refuses
  -- EVERY set.  By `Semantics.RefinementOrders.saturated→⊑T→⊑F` the failures
  -- half of `⊑F` is then implied by its trace half, and the `⊓ Stop` adds no
  -- visible behaviour, so `AnnounceSpecT`'s traces are `AnnounceSpec`'s.
  -- Together: discharging `AnnounceSafeTWith` discharges `AnnounceSafeWith`.
  ------------------------------------------------------------------------

  private
    -- the tree type the specs' `loop` iterates over
    Tree : Set → Set₁
    Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

    -- `loop`'s state-threading continuation: hand the new state back to `iter`
    κ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
    κ ms = Ret (inj₁ ms)

    -- the `iter` step `loop` builds from `AnnounceSpec`'s body …
    Step : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
    Step ms = (pchoice (announceOffer ms) ⊓ Stop) >>= κ

    -- … and the one it builds from `AnnounceSpecT`'s (no `⊓ Stop`)
    StepT : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
    StepT ms = pchoice (announceOffer ms) >>= κ

    -- `AnnounceSpec`'s state before the internal choice …
    A : Minted → Proc
    A ms = iter Step ms
    -- … the visible menu the `⊓` may pick …
    L : Minted → Proc
    L ms = iter-bind (StepT ms) Step
    -- … the `Stop` it may pick instead …
    Dead : Proc
    Dead = iter-bind (Stop >>= κ) Step
    -- … and the `sil` back-edge `loop` emits after a visible event
    S : Minted → Proc
    S ms = iter-bind (Ret ms >>= κ) Step

    -- `AnnounceSpecT`'s two states: the menu itself (no `⊓` to resolve) and
    -- the same back-edge
    AT : Minted → Proc
    AT ms = iter StepT ms
    ST : Minted → Proc
    ST ms = iter-bind (Ret ms >>= κ) StepT

    -- the two specs ARE those states at the empty minted set
    spec≡A : AnnounceSpec ≡ A []
    spec≡A = refl
    specT≡AT : AnnounceSpecT ≡ AT []
    specT≡AT = refl

    -- the internal choice's two τ-moves …
    A→L : ∀ {ms} → A ms ─[ τ ]─► L ms
    A→L = sTau {i = Lift 0ℓ (Fin 2) , fin} {a = lift fzero} refl refl
    A→Dead : ∀ {ms} → A ms ─[ τ ]─► Dead
    A→Dead = sTau {i = Lift 0ℓ (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl
    -- … and the loop-back τ
    S→A : ∀ {ms} → S ms ─[ τ ]─► A ms
    S→A = sSil refl

    -- `Dead` is `Stop` seen through the loop: stable, offering nothing, so it
    -- refuses EVERY set — this is the whole content of saturation
    dead-refuses : {X : Event√ (⊤ {0ℓ}) → Set} → Refuses Dead X
    dead-refuses = (λ _ _ → refl)
                 , λ { _ _ (_ , sRet eq)     → case eq of λ ()
                     ; _ _ (_ , sVis refl ()) }

    -- …and it has no run but the empty one
    rerouteD : ∀ {s q} → Dead ⟹⟨ s ⟩ q → Dead ⟹⟨ s ⟩ Dead
    rerouteD ⟹-refl               = ⟹-refl
    rerouteD (⟹-τ (sSil eq) _)    = case eq of λ ()
    rerouteD (⟹-τ (sTau refl ()) _)
    rerouteD (⟹-ev (sRet eq) _)   = case eq of λ ()
    rerouteD (⟹-ev (sVis refl ()) _)

    -- the announce channel's gate: whichever way it decides, an offer it makes
    -- is a `Ret` (the loop-back), never anything else
    gate-Ret : (b : Bool) (ms : Minted) {t : Tree Minted}
             → (if b then just (Ret ms) else nothing) ≡ just t
             → Σ[ ms′ ∈ Minted ] t ≡ Ret ms′
    gate-Ret true  ms refl = ms , refl
    gate-Ret false ms ()

    -- EVERY offer of the shared menu is a `Ret`: the spec's state changes only
    -- through `loop`, so a visible step always lands on the loop-back edge
    menu-Ret : ∀ ms (at : AnyTypes (Net_Api Payload)) (a : proj₁ at) {t : Tree Minted}
             → announceOffer ms at a ≡ just t → Σ[ ms′ ∈ Minted ] t ≡ Ret ms′
    menu-Ret ms (_ , input  _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , output _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , sndmsg _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , rcvmsg _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , tx     _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , sndack _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , rcvack _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , ack    _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , done   _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , apiCS  _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , apiBF  _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , apiTS  _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , apiKA  _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , apiLF  _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , store  _ _ _) _ refl = ms , refl
    menu-Ret ms (_ , break  _)     _ refl = ms , refl
    -- the mint channel grows the minted set …
    menu-Ret ms (_ , env _ _ envMint) (just e  , _) refl = (ebHash e ∷ ms) , refl
    menu-Ret ms (_ , env _ _ envMint) (nothing , _) refl = ms , refl
    -- … and the announce channel is the gated one; the rest of LeiosNotify is free
    menu-Ret ms (_ , apiLN _ _ sendLNBlockAnnouncement) h eq = gate-Ret (announceOK ms h) ms eq
    menu-Ret ms (_ , apiLN _ _ sendLNRequestNext)       _ refl = ms , refl
    menu-Ret ms (_ , apiLN _ _ sendLNDone)              _ refl = ms , refl
    menu-Ret ms (_ , apiLN _ _ sendLNBlockOffer)        _ refl = ms , refl
    menu-Ret ms (_ , apiLN _ _ sendLNBlockTxsOffer)     _ refl = ms , refl
    menu-Ret ms (_ , apiLN _ _ sendLNVotesOffer)        _ refl = ms , refl
    menu-Ret ms (_ , apiLN _ _ recvLNBlockAnnouncement) _ refl = ms , refl
    menu-Ret ms (_ , apiLN _ _ recvLNBlockOffer)        _ refl = ms , refl
    menu-Ret ms (_ , apiLN _ _ recvLNBlockTxsOffer)     _ refl = ms , refl
    menu-Ret ms (_ , apiLN _ _ recvLNVotesOffer)        _ refl = ms , refl

    -- the menu node itself, and the node it becomes under `loop`'s state threading —
    -- named so the `iterV`/`bindV` peeling lemmas below can be pointed at them
    Nmenu : Minted → NodeKind (Net_Api Payload) (ExtI (Net_Api Payload)) Minted
    Nmenu ms = react (announceOffer ms) ∅t
    Xmenu : Minted → NodeKind (Net_Api Payload) (ExtI (Net_Api Payload)) (Minted ⊎ ⊤ {0ℓ})
    Xmenu ms = react (bindV κ (Nmenu ms)) (bindT κ (Nmenu ms))

    -- BOTH specs run the SAME menu (they differ only in the `⊓ Stop` above it), so a
    -- visible step of the one built with `k` lands on the loop-back edge, and the very
    -- same event steps the one built with `k′` to the corresponding edge
    menu-step : ∀ {ms} (k k′ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})) {e q}
              → iter-bind (StepT ms) k ─[ ev e ]─► q
              → Σ[ ms′ ∈ Minted ]
                  ((q ≡ iter-bind (Ret ms′ >>= κ) k)
                   × (iter-bind (StepT ms) k′ ─[ ev e ]─► iter-bind (Ret ms′ >>= κ) k′))
    menu-step k k′ (sRet eq) = case eq of λ ()
    menu-step {ms} k k′ (sVis {at = at} {a = a} refl br) with iterV-elim k (Xmenu ms) {at = at} {a = a} br
    ... | t₁ , eq₁ , refl with bindV-elim κ (Nmenu ms) {at = at} {a = a} eq₁
    ...   | t₂ , eq₂ , refl with menu-Ret ms at a eq₂
    ...     | ms′ , refl =
              ms′ , refl
                  , sVis refl (iterV-eq k′ (Xmenu ms) {at = at} {a = a}
                                (bindV-eq κ (Nmenu ms) {at = at} {a = a} eq₂))

    -- REROUTING: whatever run `AnnounceSpec` makes, the SAME trace can be run into the
    -- `Stop` branch instead — take it at the last internal choice before stopping
    rerouteA : ∀ {ms s q} → A ms ⟹⟨ s ⟩ q → A ms ⟹⟨ s ⟩ Dead
    rerouteL : ∀ {ms s q} → L ms ⟹⟨ s ⟩ q → A ms ⟹⟨ s ⟩ Dead
    rerouteS : ∀ {ms s q} → S ms ⟹⟨ s ⟩ q → S ms ⟹⟨ s ⟩ Dead

    rerouteA ⟹-refl            = ⟹-τ A→Dead ⟹-refl
    rerouteA (⟹-τ (sSil eq) _) = case eq of λ ()
    rerouteA (⟹-τ (sTau {i = _ , base _}   refl ()) _)
    rerouteA (⟹-τ (sTau {i = _ , pair _ _} refl ()) _)
    rerouteA (⟹-τ (sTau {i = _ , fin} {a = lift fzero}          refl refl) rest) =
      rerouteL rest
    rerouteA (⟹-τ (sTau {i = _ , fin} {a = lift (fsuc fzero)}   refl refl) rest) =
      ⟹-τ A→Dead (rerouteD rest)
    rerouteA (⟹-τ (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ()) _)
    rerouteA (⟹-ev (sRet eq) _)     = case eq of λ ()
    rerouteA (⟹-ev (sVis refl ()) _)

    rerouteL ⟹-refl              = ⟹-τ A→Dead ⟹-refl
    rerouteL (⟹-τ (sSil eq) _)   = case eq of λ ()
    rerouteL (⟹-τ (sTau refl ()) _)
    rerouteL (⟹-ev st rest) with menu-step Step Step st
    ... | ms′ , refl , _ = ⟹-τ A→L (⟹-ev st (rerouteS rest))

    rerouteS ⟹-refl                  = ⟹-τ S→A (⟹-τ A→Dead ⟹-refl)
    rerouteS (⟹-τ (sSil refl) rest)  = ⟹-τ S→A (rerouteA rest)
    rerouteS (⟹-τ (sTau eq _) _)     = case eq of λ ()
    rerouteS (⟹-ev (sRet eq) _)      = case eq of λ ()
    rerouteS (⟹-ev (sVis eq _) _)    = case eq of λ ()

    -- SIMULATION: `AnnounceSpec` runs every trace `AnnounceSpecT` runs — it just
    -- resolves the `⊓` towards the menu first
    simA : ∀ {ms s q} → AT ms ⟹⟨ s ⟩ q → Σ[ q′ ∈ Proc ] (A ms ⟹⟨ s ⟩ q′)
    simS : ∀ {ms s q} → ST ms ⟹⟨ s ⟩ q → Σ[ q′ ∈ Proc ] (S ms ⟹⟨ s ⟩ q′)

    simA ⟹-refl            = _ , ⟹-refl
    simA (⟹-τ (sSil eq) _) = case eq of λ ()
    simA (⟹-τ (sTau refl ()) _)
    simA (⟹-ev st rest) with menu-step StepT Step st
    ... | ms′ , refl , stF with simS rest
    ...   | q′ , run = q′ , ⟹-τ A→L (⟹-ev stF run)

    simS ⟹-refl                 = _ , ⟹-refl
    simS (⟹-τ (sSil refl) rest) with simA rest
    ... | q′ , run = q′ , ⟹-τ S→A run
    simS (⟹-τ (sTau eq _) _)    = case eq of λ ()
    simS (⟹-ev (sRet eq) _)     = case eq of λ ()
    simS (⟹-ev (sVis eq _) _)   = case eq of λ ()

  -- SATURATION: every trace of `AnnounceSpec` carries a failure for EVERY refusal set,
  -- because the trace can be re-run into the `⊓`'s `Stop` branch
  announceSpec-saturated : Saturated AnnounceSpec
  announceSpec-saturated (_ , run) = Dead , rerouteA run , dead-refuses

  -- THE LOAD-BEARING STEP of the collapse: `Stop` contributes no visible behaviour, so
  -- every trace of the lean `AnnounceSpecT` is a trace of the Chaos-shaped
  -- `AnnounceSpec` (the direction `⊑T`-transport needs)
  announceSpecT-traces⊆ : ∀ s → traces AnnounceSpecT s → traces AnnounceSpec s
  announceSpecT-traces⊆ s (_ , run) = simA run

  -- THE COLLAPSE: discharging the `⊑T` family discharges the `⊑F` one, at any medium —
  -- so the two parallel families need only ONE campaign, the `⊑T` one
  announceSafeT→announceSafe : (med : Proc) → AnnounceSafeTWith med → AnnounceSafeWith med
  announceSafeT→announceSafe med h =
    saturated→⊑T→⊑F announceSpec-saturated (λ s tr → announceSpecT-traces⊆ s (h s tr))

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE LOOPING RELAY NODE LOGIC (§4.3 of
-- `docs/superpowers/specs/2026-08-11-n-node-network-properties-design.md`).
--
-- `Parametric.Node` supplies the *scaffolding* — `node n lg = linkBundles
-- n ∥⇘ apiES ⇙ lg` — but leaves `lg` open; the only witnesses so far are
-- `Skip` (the line/star instances) and the four hand-written one-shot
-- `produce`/`consume` scripts of `FourNode.FourNodeDiamond`.  This module
-- supplies the real thing: a topology-generic RELAY node that keeps
-- fetching, storing and serving blocks indefinitely.
--
-- SHAPE
--
--   nodeLogic n held
--     = (mint n ⦀ ⦀⁺ (endpointThreads n e₀) (map (endpointThreads n) es))
--         ∥⇘ storeES ⇙ blockStore n held
--
-- with `endpointThreads n (l , d) = clientLoop n (l , d) ⦀ serverLoop n
-- (l , d)`, one such pair per incident endpoint of `n`.
--
-- DELIBERATE DEVIATION FROM §4.3.  The design sketch groups the threads
-- as `⦀⁺ clientLoops ⦀ ⦀⁺ serverLoops` (all clients, then all servers).
-- They are grouped PER ENDPOINT here instead.  The two are the same set
-- of threads, but the per-endpoint grouping is the one that lines up
-- component-for-component with `linkBundles n = ⦀⁺ (bundleAt e₀) (map
-- bundleAt es)`, so the regrouping the compositional spec route needs
-- (`InterchangeGoal` below) is a single bundle/thread interchange rather
-- than an interchange PLUS an ⦀-permutation.  This was found by drafting
-- `nodeSpec` alongside the logic, which is exactly what that draft is for.
--
-- LOOPING WITHOUT HAND-ROLLED CORECURSION.  Every thread is `loop0
-- body` and the store is `loop storeStep held` (`CSP.Operators`), both
-- built on the `sil`-guarded `iter`.  No coinductive definition is
-- written here at all, so the repo's productivity hazard (recursive
-- calls must sit syntactically under a constructor; helper-bound
-- coinductive functions break the checker) simply does not arise.
--
-- DIVERGENCE-FREEDOM BY CONSTRUCTION.  `iter` loops back guarded by one
-- `sil`, so a loop body performing NO visible event would be a pure
-- τ-loop.  `∖ ioES` hides only `input`/`output` (`NetCommon.ioSet-dec`
-- answers `no` for every `api*`/`done`, and `NetworkPar`'s ι-renamings
-- map api events to api events), so api events survive hiding.  Every
-- loop body below therefore performs at least one visible event per
-- pass — see the per-thread comments, and the summary table:
--
--   mint        : `env home(n) envMint`           (the mint channel)
--   clientLoop  : `apiCS l d sendCSRequestNext`   (+ 3 more api events)
--   serverLoop  : `apiCS l d reqCSRequestNext`    (+ 5 more api events)
--   store       : one of mint / put / get         (every branch is a prefix)
--
-- NO `done`, ANYWHERE.  `done` is api-synced, so a peer can only tear
-- down if the logic offers it.  None of these loops ever does, which is
-- what keeps a relay node perpetual and dodges the 2026-07-07
-- "done-quiescence" deadlock of `System_CopySpec`.
--
-- THE STORE CHANNELS.  A node's store rendezvous has its OWN `Net_Api`
-- channels, `store l d stPut` / `store l d stGet`, and the environment's
-- mint has `env l d envMint`.  An earlier draft rode all three on `tx`
-- with three different `IDs` tags; that was a latent bug, because `tx` is
-- the mux's INTERNAL channel — `Network.agda:17` hides it
-- (`(TxSide [|{| tx, ack |}|] RxSide) \ {| tx, ack |}`), so the reuse only
-- looked free while the scenarios ran `CopySpec*` rather than the real
-- `NetworkA`.  The node is named in the alphabet by its HOME endpoint (the
-- head of `endpointsOf n`), which `endpoints-sound` makes unique to it.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.NodeLogic where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes; no)
open import Class.DecEq using (DecEq)
import Class.DecEq.Instances as DecEqI

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O

------------------------------------------------------------------------
-- The generic layer
------------------------------------------------------------------------

-- the relay logic, parametric in the network parameters, the topology and the api
-- alphabet — the same three parameters `Parametric.Node` and `Parametric.Assembly`
-- take, so `node`/`systemOf` below are literally that module's
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (Block; EB; time₀; length₀; decBlock)
  open import Data.Maybe using (Maybe)
  open import CSP.Examples.Cardano_network.Base
    using ( Dir; FromInitiator
          ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission )
  open N p
    using ( Link; Net_Api; Net_Api-≟
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; store; env; break
          ; stPut; stGet; envMint
          ; reqCSRequestNext; sendCSAwaitReply; sendCSRollForward
          ; sendCSRequestNext; recvCSRollforward
          ; reqBFRange; sendBFStartBatch; sendBFBlock; sendBFBatchDone
          ; sendBFRequestRange; recvBFBlock )
  open D p
    using ( Payload; Point; Header; Tip; ChainRange
          ; point; header; tip; chainRange
          ; MsgBlock; blockFetch
          ; DecEq-Point; DecEq-Header; DecEq-Tip; DecEq-ChainRange
          ; DecEq-Payload )
  open Topology t using (Node; endpointsOf)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using ( EventSet; chanSet; _∥⇘_⇙_; _⦀_; ⦀⁺; _□_
          ; Skip; Stop; Ret; Prefix; Prefix₀; Output; loop; loop0 )
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES
    using (Proc; bundleAt; node)
  open import Semantics.FailuresDivergences
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⊑FD_)

  -- product `DecEq` for the `sendCSRollForward` carrier (`Header × Tip`), needed by
  -- the `!`-output in `serverBody-k` (cf. the identical instance in `FourNodeDiamond`)
  instance
    DecEq-Header×Tip : DecEq (Header × Tip)
    DecEq-Header×Tip = DecEqI.DecEq-×

  -- the store's own state type: the blocks a node currently holds
  Held : Set
  Held = List Block

  -- a store step returns the (possibly grown) store state, so it is not a `Proc`
  StoreProc : Set₁
  StoreProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Held

  ------------------------------------------------------------------------
  -- The store alphabet
  ------------------------------------------------------------------------

  -- a node's HOME endpoint — the head of its incident-endpoint list.  `endpoints-
  -- sound` makes an endpoint unique to one node, so this names the node on the
  -- node-local `store`/`env` channels.
  homeOf : Node → Link × Dir
  homeOf n = proj₁ (endpointsOf n)

  -- the MINT channel of `n`: the environment injects a fresh RB (and, one day, the
  -- EB it announces) into `n`'s store
  mintEv : Node → Net_Api Payload (Maybe EB × Block)
  mintEv n = env (proj₁ (homeOf n)) (proj₂ (homeOf n)) envMint

  -- the PUT channel of `n`: a client thread deposits a block it has just fetched
  -- (this event IS the observable "block `b` arrived at node `n`")
  putEv : Node → Net_Api Payload Block
  putEv n = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) stPut

  -- the GET channel of `n`: a server thread takes a held block to serve it
  getEv : Node → Net_Api Payload Block
  getEv n = store (proj₁ (homeOf n)) (proj₂ (homeOf n)) stGet

  -- membership of the store rendezvous set: EVERY `store`/`env` channel.  Node-
  -- uniform on purpose — nodes are interleaved by `systemOf`'s `⦀Fin⁺`, so one
  -- node's `∥⇘ storeES ⇙` never meets another node's store, and inside a node only
  -- that node's own three channels ever occur.
  storeSet : AnyTypes (Net_Api Payload) → Set
  storeSet (_ , store _ _ _) = ⊤
  storeSet (_ , env   _ _ _) = ⊤
  storeSet _                 = ⊥

  -- decidability of `storeSet` membership (one clause per `Net_Api` constructor)
  storeSet-dec : (at : AnyTypes (Net_Api Payload)) → Dec (storeSet at)
  storeSet-dec (_ , store  _ _ _) = yes tt
  storeSet-dec (_ , env    _ _ _) = yes tt
  storeSet-dec (_ , tx     _ _ _) = no λ ()
  storeSet-dec (_ , input  _ _ _) = no λ ()
  storeSet-dec (_ , output _ _ _) = no λ ()
  storeSet-dec (_ , sndmsg _ _ _) = no λ ()
  storeSet-dec (_ , rcvmsg _ _ _) = no λ ()
  storeSet-dec (_ , sndack _ _ _) = no λ ()
  storeSet-dec (_ , rcvack _ _ _) = no λ ()
  storeSet-dec (_ , ack    _ _ _) = no λ ()
  storeSet-dec (_ , done   _ _ _) = no λ ()
  storeSet-dec (_ , apiCS  _ _ _) = no λ ()
  storeSet-dec (_ , apiBF  _ _ _) = no λ ()
  storeSet-dec (_ , apiTS  _ _ _) = no λ ()
  storeSet-dec (_ , apiKA  _ _ _) = no λ ()
  storeSet-dec (_ , apiLN  _ _ _) = no λ ()
  storeSet-dec (_ , apiLF  _ _ _) = no λ ()
  storeSet-dec (_ , break  _)     = no λ ()

  -- the store rendezvous alphabet (disjoint from `apiES` and from `ioES`, so store
  -- events survive `∖ ioES` and are observable in `systemOf`)
  storeES : EventSet
  storeES = chanSet storeSet storeSet-dec

  ------------------------------------------------------------------------
  -- The store
  ------------------------------------------------------------------------

  -- offer `get ! b` for every block of `bs`, leaving the state `held` intact.  Blocks
  -- are NEVER removed: once held, a block stays offered forever, which is what makes
  -- the monotone "the set of nodes holding b only grows" invariant of §6.2 true.
  offerHeld : Node → Held → Held → StoreProc
  offerHeld n held []       = Stop
  offerHeld n held (b ∷ bs) = (getEv n ! b ⟶ Ret held) □ offerHeld n held bs

  -- one store step: accept a mint (keeping only its RB for now), accept a deposit,
  -- or hand over any held block.  Every branch is a visible prefix, so the store's
  -- loop can never τ-cycle.
  storeStep : Node → Held → StoreProc
  storeStep n held =
      (mintEv n ⟶ (λ mb → Ret (proj₂ mb ∷ held)))
    □ ((putEv n ⟶ (λ b → Ret (b ∷ held)))
    □  offerHeld n held held)

  -- the node's block store holding `held`: a stateful forever loop threading `Held`
  -- (named `blockStore`, not `store`: `store` is now a `Net_Api` channel)
  blockStore : Node → Held → Proc
  blockStore n held = loop (storeStep n) held

  ------------------------------------------------------------------------
  -- The threads
  ------------------------------------------------------------------------

  -- the mint thread: the origin of every block in the network.  VISIBLE EVENT PER
  -- PASS: `env home(n) envMint` (the mint channel).
  mint : Node → Proc
  mint n = loop0 (mintEv n ⟶₀ Skip)

  -- the RollForward continuation of a client round: request the announced block's
  -- range, receive the block and deposit it in the store.  VISIBLE EVENTS:
  -- `apiBF sendBFRequestRange`, `apiBF recvBFBlock`, `store home(n) stPut` (put).
  clientBody-k : Node → Link → Dir → Header × Tip → Proc
  clientBody-k n l d (header b , _) =
    (apiBF l d sendBFRequestRange ! chainRange (point b) (point b) ⟶
      (apiBF l d recvBFBlock ⟶ (λ b′ → (putEv n ! b′ ⟶ Skip))))

  -- one client round on endpoint `(l , d)`: ask the far end for the next header, then
  -- fetch and store the announced block.  This is `FourNodeDiamond.consume` MINUS its
  -- trailing `sendBFClientDone`/`sendCSDone` — dropping them is what lets the round
  -- repeat, since both peers return to `stIdle` on their own (BlockFetch via the
  -- hidden `MsgBatchDone`, ChainSync straight after `MsgCSRollForward`).
  -- VISIBLE EVENT PER PASS: `apiCS l d sendCSRequestNext` (first of four).
  clientBody : Node → Link → Dir → Proc
  clientBody n l d =
    apiCS l d sendCSRequestNext ⟶₀
      (apiCS l d recvCSRollforward ⟶ clientBody-k n l d)

  -- the client thread on endpoint `(l , d)`: a client round, forever
  clientLoop : Node → Link × Dir → Proc
  clientLoop n ld = loop0 (clientBody n (proj₁ ld) (proj₂ ld))

  -- the tail of a server round, on the block the store handed over: announce it via
  -- ChainSync (through `stMustReply`, Praos-faithful, as `FourNodeDiamond.produce`
  -- does) and serve it as a one-block BlockFetch batch.  The `get` channel now
  -- carries a `Block` outright, so there is no payload to decode and no unreachable
  -- fallback clause to justify.
  serverBody-k : Node → Link → Dir → Block → Proc
  serverBody-k n l d b =
    apiCS l d sendCSAwaitReply ⟶₀
      ((apiCS l d sendCSRollForward ! (header b , tip b) ⟶
        (apiBF l d reqBFRange ⟶ (λ _ →
          apiBF l d sendBFStartBatch ⟶₀
            ((apiBF l d sendBFBlock ! b ⟶
              (apiBF l d sendBFBatchDone ⟶₀ Skip)))))))

  -- one server round on endpoint `(l , d)`: await the far end's RequestNext (reported
  -- by the ChainSync server peer as `reqCSRequestNext`), take a held block from the
  -- store, announce it and serve it.  This is `FourNodeDiamond.produce` with the
  -- block read from the store instead of being baked in, and MINUS its two trailing
  -- driven `done`s, so the round repeats.
  -- VISIBLE EVENT PER PASS: `apiCS l d reqCSRequestNext` (first of six).
  serverBody : Node → Link → Dir → Proc
  serverBody n l d =
    apiCS l d reqCSRequestNext ⟶₀
      (getEv n ⟶ serverBody-k n l d)

  -- the server thread on endpoint `(l , d)`: a server round, forever
  serverLoop : Node → Link × Dir → Proc
  serverLoop n ld = loop0 (serverBody n (proj₁ ld) (proj₂ ld))

  -- BOTH threads of one endpoint.  This pairing — not the §4.3 client-fold /
  -- server-fold pairing — is what makes the logic line up component-for-component
  -- with `linkBundles`, see the header note.
  endpointThreads : Node → Link × Dir → Proc
  endpointThreads n ld = clientLoop n ld ⦀ serverLoop n ld

  -- every incident endpoint's thread pair, interleaved in `endpointsOf`'s order
  -- (`⦀` is not commutative up to `≡`, so that order is part of the interface)
  allThreads : Node → Proc
  allThreads n =
    ⦀⁺ (endpointThreads n (proj₁ (endpointsOf n)))
       (map (endpointThreads n) (proj₂ (endpointsOf n)))

  -- THE RELAY NODE LOGIC: the mint thread and every endpoint's client/server pair,
  -- all interleaved, synchronised with the node's block store on `storeES`.  Passed
  -- as `Parametric.Node`'s `lg` argument it turns the scaffolding into a real
  -- N-node network; `systemOf (λ n → nodeLogic n [])` is that network.
  nodeLogic : Node → Held → Proc
  nodeLogic n held = (mint n ⦀ allThreads n) ∥⇘ storeES ⇙ blockStore n held

  ------------------------------------------------------------------------
  -- DRAFT node specification — NOT proved, stated to size the next milestone
  --
  -- Under `⊑FD` a spec may only ADD refusals, while a must-offer property asserts
  -- refusals are ABSENT (the structural limitation recorded at
  -- `FourNode/Liveness/CSP_Refinement/Spec.lagda.md:929-945`), so a node spec cannot
  -- abstract away the per-endpoint protocol PHASE: whether `getEv n` is offered in a
  -- stable state depends on where each server thread sits in its round.  A single
  -- monolithic `nodeSpec` would therefore have a phase-product state space, of size
  -- exponential in the node's degree — not viable for a spec that must be generic in
  -- the degree.
  --
  -- The tractable shape is the COMPOSITIONAL one below: the spec mirrors the logic's
  -- own parallel structure, one abstract component per endpoint over the SAME store.
  ------------------------------------------------------------------------

  -- the DRAFT node spec, parametric in whatever one endpoint's abstraction turns out
  -- to be: the endpoint abstractions interleaved, against the node's real store
  nodeSpec : (Node → Link × Dir → Proc) → Node → Held → Proc
  nodeSpec epSpec n held =
    (⦀⁺ (epSpec n (proj₁ (endpointsOf n))) (map (epSpec n) (proj₂ (endpointsOf n))))
      ∥⇘ storeES ⇙ blockStore n held

  -- the per-node obligation Milestone 4 must discharge, as a type
  NodeObligation : (Node → Link × Dir → Proc) → Set₁
  NodeObligation epSpec = ∀ n held → nodeSpec epSpec n held ⊑FD node n (nodeLogic n held)

  -- one endpoint's IMPLEMENTATION slice: its mini-protocol bundle synchronised, on
  -- `apiES`, with exactly the two threads that drive it
  endpointImpl : Node → Link × Dir → Proc
  endpointImpl n ld = bundleAt ld ∥⇘ apiES ⇙ endpointThreads n ld

  -- the per-endpoint obligation the compositional route would leave, as a type: a
  -- SINGLE goal, independent of the node's degree and of the number of nodes
  EndpointObligation : (Node → Link × Dir → Proc) → Set₁
  EndpointObligation epSpec = ∀ n ld → epSpec n ld ⊑FD endpointImpl n ld

  -- THE MISSING LAW, as a type.  `EndpointObligation` + `⦀⁺-mono-⊑FD` +
  -- `∥-mono-⊑FD` give `NodeObligation` ONLY through this regrouping, which says the
  -- bundles may be pushed inside the thread interleaving.  It is the standard CSP
  -- parallel/interleave interchange and its side conditions all hold here (distinct
  -- endpoints' bundle alphabets are disjoint; each thread pair's api events are
  -- confined to its own endpoint; `mint` performs no `apiES` event; `storeES` is
  -- disjoint from `apiES`) — but NO law of this shape exists anywhere in the repo,
  -- and it is not derivable from `ParallelMonoFD`'s monotonicity lemmas alone.
  -- Sizing it is the first thing Milestone 4 should do.
  InterchangeGoal : Set₁
  InterchangeGoal = ∀ n held →
      ((mint n ⦀ (⦀⁺ (endpointImpl n (proj₁ (endpointsOf n)))
                     (map (endpointImpl n) (proj₂ (endpointsOf n)))))
         ∥⇘ storeES ⇙ blockStore n held)
    ⊑FD node n (nodeLogic n held)

------------------------------------------------------------------------
-- Sanity check: the relay logic at the three-node line
--
-- `Parametric.LineInstance` witnesses `systemOf (λ _ → Skip)` — the
-- scaffolding over a DERIVED `endpointsOf`.  This is the same witness
-- with the trivial logic replaced by the real relay logic, every node
-- starting from an empty store.  The line's degree-2 middle node
-- exercises the non-empty-tail path through `⦀⁺` and its two degree-1
-- ends exercise the `⦀⁺ P [] = P` path.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Parametric.LineInstance
  using (lineParams; line)
open import CSP.Examples.Cardano_network.ApiAlphabet lineParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node lineParams line apiES
  using (Proc; systemOf)

-- the three-node line running the relay logic at every node, each store initially
-- empty: a TYPECHECKING WITNESS that `nodeLogic` really is a `Parametric.Node` `lg`
lineRelaySystem : Proc
lineRelaySystem = systemOf (λ n → Generic.nodeLogic lineParams line apiES n [])

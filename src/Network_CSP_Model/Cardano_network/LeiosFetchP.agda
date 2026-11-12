{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the LEIOS-PROTOTYPE LeiosFetch peers.
--
-- Mirrors the other peer modules.  Role mapping (Ouroboros naming):
-- `clientStepP` = the CONSUMER (initiator: drives fetch requests via api,
-- runs delivery handlers on receive); `serverStepP` = the PRODUCER (waits for
-- the request off the wire, REPORTS it, then delivers via api).  Wire events
-- `sendLFP`/`receiveLFP` negotiate `Payload`; api/done are peer-local.
-- Productive via `iter` (no NON_TERMINATING).
--
-- This module models the Leios mini-protocol as implemented on the `leios-prototype`
-- branch of ouroboros-consensus (`LeiosDemoOnlyTest{Notify,Fetch}.hs`, protocol numbers
-- 18/19), which adapts the CIP-164 draft of July 2026.  Messages, payload types, state
-- machine and agency follow the prototype, with `TxBitmap` represented as concrete
-- offsets and `MsgLFPBlockTxs` carrying transactions in that requested order, without
-- an echoed point or bitmap (see decision D5 in
-- docs/specs/2026-11-11-leiosfetch-upstream-alignment-design.md).
-- The application API retains offset-indexed entries;
-- a count-mismatched BlockTxs reply is received, then the client stops inside its
-- step, at the scope of this peer; whole-connection death is not modeled here.
-- Pipelining and credits, vote weights, deadlines, equivocation and
-- freshness are abstracted (peers are depth-1 alternating machines; the oracles
-- `certifies`, `ebSize`, `ebTxs` stand in for validation).  The older CIP-draft model
-- (`LeiosNotify.agda`/`LeiosFetch.agda`, `apiLN`/`apiLF`) stays beside this one: both ride
-- the same protocol ids and wire channels, and a node runs one or the other by the bundle
-- builder passed to `Node.nodeWith` (`nodeBundle` / `nodeBundleR` versus `nodeBundleP`).
-- Theorems about the old peers (`announceSafeT`, `bfOverLf`, the four-node liveness estate)
-- are untouched by this module.
--
-- "Protocol numbers 18/19" is the PROTOTYPE's numbering: the model's `Base.IDs` is a plain
-- six-constructor enum (`N2N_LeiosNotify`, `N2N_LeiosFetch`) and carries no numeric tag.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.LeiosFetchP (p : Params) where

open import Level renaming (zero to lzero)
import Data.Unit.Polymorphic as Poly
open import Data.Unit using (⊤)
open import Data.Bool using (true; false)
open import Data.Nat using (_<ᵇ_)
open import Cardano_network.Replay.LeiosFetchWire using (maxTxs)
open import Cardano_network.Replay.LeiosFetchWords using (decodable)
open import Data.List using (List; length; zip; map)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees

open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net  p

open Params p

------------------------------------------------------------------------
-- Step 1: the per-protocol event type `LFPEv`.
------------------------------------------------------------------------

-- the leios-prototype LeiosFetch peer alphabet
data LFPEv : Set → Set where
  sendLFP    : Link → Dir → LFPEv Payload   -- peer→net (→ input)
  receiveLFP : Link → Dir → LFPEv Payload   -- net→peer (→ output)
  apiLPev    : (l : Link) (d : Dir) (m : ApiLPTag) → LFPEv (ApiLPCar m)  -- peer-local
  doneLFP    : Link → Dir → LFPEv ⊤          -- peer-local: Done

------------------------------------------------------------------------
-- Step 2: decidable equality on `AnyTypes LFPEv`.
------------------------------------------------------------------------

-- decidable equality on existential-wrapped prototype LeiosFetch events
LFPEv-≟ : (x y : AnyTypes LFPEv) → Dec (x ≡ y)
LFPEv-≟ = go
  where
  go : (x y : AnyTypes LFPEv) → Dec (x ≡ y)
  go (_ , sendLFP l₁ d₁)     (_ , sendLFP l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , receiveLFP l₁ d₁)  (_ , receiveLFP l₂ d₂)  with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiLPev l₁ d₁ m₁) (_ , apiLPev l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneLFP l₁ d₁)     (_ , doneLFP l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendLFP _ _)    (_ , receiveLFP _ _) = no λ ()
  go (_ , sendLFP _ _)    (_ , apiLPev _ _ _)  = no λ ()
  go (_ , sendLFP _ _)    (_ , doneLFP _ _)    = no λ ()
  go (_ , receiveLFP _ _) (_ , sendLFP _ _)    = no λ ()
  go (_ , receiveLFP _ _) (_ , apiLPev _ _ _)  = no λ ()
  go (_ , receiveLFP _ _) (_ , doneLFP _ _)    = no λ ()
  go (_ , apiLPev _ _ _)  (_ , sendLFP _ _)    = no λ ()
  go (_ , apiLPev _ _ _)  (_ , receiveLFP _ _) = no λ ()
  go (_ , apiLPev _ _ _)  (_ , doneLFP _ _)    = no λ ()
  go (_ , doneLFP _ _)    (_ , sendLFP _ _)    = no λ ()
  go (_ , doneLFP _ _)    (_ , receiveLFP _ _) = no λ ()
  go (_ , doneLFP _ _)    (_ , apiLPev _ _ _)  = no λ ()

------------------------------------------------------------------------
-- Step 3: return type + carrier DecEq instances.
------------------------------------------------------------------------

-- the peers return the unit on √
Rr : Set
Rr = Poly.⊤ {lzero}

instance
  -- trivial decidable equality on the unit return type
  DecEq-Rr : DecEq Rr
  DecEq-Rr = record { _≟_ = λ _ _ → yes refl }

-- The `!`-output carriers that need a `DecEq` — `EBHash × LSlot`,
-- `(EBHash × LSlot) × TxBitmap` and `(EBHash × LSlot) × List (ℕ × Tx)` — are supplied
-- EXPLICITLY at each `Output` site from `Data.agda`'s NAMED instance terms
-- (`DecEq-EBPoint`, `DecEq-TxsRequest`, `DecEq-TxsReply`).  A local named instance would
-- both make the components of a `×` carrier ambiguous during instance search
-- (`LeiosFetch.agda:114-120`) and hand the `Output` a different-but-equal term from the one
-- a later `≡`-probe or `OffersOnly` obligation reconstructs.

import CSP.Operators {E = LFPEv} as LFPOps
open LFPOps LFPEv-≟

------------------------------------------------------------------------
-- Step 4: unified peer state (both peers walk the same FSM; agency differs).
------------------------------------------------------------------------

-- the leios-prototype LeiosFetch peer state.  The prototype's `StBusy StBlock` /
-- `StBusy StBlockTxs` nesting is a Haskell typing device, flattened here.
data LFPState : Set where
  stIdle     : LFPState   -- consumer requests / producer awaits a request
  stBlock    : LFPState   -- EB delivery outstanding
  stBlockTxs : EBHash × LSlot → TxBitmap → LFPState -- outstanding tx-closure request
  stDone     : LFPState   -- terminal (√)

instance
  -- decidable equality on the unified prototype LeiosFetch state
  DecEq-LFPState : DecEq LFPState
  DecEq-LFPState ._≟_ = go
    where
    go : (x y : LFPState) → Dec (x ≡ y)
    go stIdle     stIdle     = yes refl
    go stBlock    stBlock    = yes refl
    go (stBlockTxs q bm) (stBlockTxs q′ bm′)
      with _≟_ ⦃ DecEq-EBPoint ⦄ q q′ | _≟_ ⦃ DecEq-TxBitmap ⦄ bm bm′
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go stDone     stDone     = yes refl
    go stIdle     stBlock    = no λ ()
    go stIdle     (stBlockTxs _ _) = no λ ()
    go stIdle     stDone     = no λ ()
    go stBlock    stIdle     = no λ ()
    go stBlock    (stBlockTxs _ _) = no λ ()
    go stBlock    stDone     = no λ ()
    go (stBlockTxs _ _) stIdle     = no λ ()
    go (stBlockTxs _ _) stBlock    = no λ ()
    go (stBlockTxs _ _) stDone     = no λ ()
    go stDone     stIdle     = no λ ()
    go stDone     stBlock    = no λ ()
    go stDone     (stBlockTxs _ _) = no λ ()

------------------------------------------------------------------------
-- Step 5: the client (consumer) peer.
------------------------------------------------------------------------

-- one consumer step (the body of the `iter` loop)
clientStepP : Link → Dir → LFPState → PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)
clientStepP l d stIdle = pchoice v
  where
  v : (at : AnyTypes LFPEv)
    → ContinueType at (Maybe (PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)))
  v (_ , apiLPev l′ d′ lfpSendBlockRequest) q with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLFP l d !
           (time₀ , FromInitiator , length₀ , leiosFetchP (MsgLFPBlockRequest q)) ⟶
           Ret (inj₁ stBlock))
  ... | _        | _        = nothing
  v (_ , apiLPev l′ d′ lfpSendBlockTxsRequest) (q , bm) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLFP l d !
           (time₀ , FromInitiator , length₀ , leiosFetchP (MsgLFPBlockTxsRequest q bm)) ⟶
           Ret (inj₁ (stBlockTxs q bm)))
  ... | _        | _        = nothing
  v (_ , apiLPev l′ d′ lfpSendDone) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLFP l d ! (time₀ , FromInitiator , length₀ , leiosFetchP MsgLFPDone) ⟶
           Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , sendLFP _ _)    _ = nothing
  v (_ , receiveLFP _ _) _ = nothing
  v (_ , doneLFP _ _)    _ = nothing
clientStepP l d stBlock = pchoice v
  where
  v : (at : AnyTypes LFPEv)
    → ContinueType at (Maybe (PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)))
  -- the reply carries NO point: the client keys on the point it requested (spec §2.2)
  v (_ , receiveLFP l′ d′) (_ , _ , _ , leiosFetchP (MsgLFPBlock eb)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiLPev l d lfpRecvBlock ! eb ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveLFP _ _) _ = nothing
  v (_ , sendLFP _ _)    _ = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , doneLFP _ _)    _ = nothing
clientStepP l d (stBlockTxs q bm) = pchoice v
  where
  v : (at : AnyTypes LFPEv)
    → ContinueType at (Maybe (PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)))
  -- No point is echoed: pair the positional reply with the stored request's bitmap.
  -- Apply the decoder cap before the count check and zip; stop as upstream's
  -- client errors and the connection dies, without reporting an API reply.
  v (_ , receiveLFP l′ d′) (_ , _ , _ , leiosFetchP (MsgLFPBlockTxs txs))
    with l′ ≟ l | d′ ≟ d | maxTxs <ᵇ length txs
  ... | yes refl | yes refl | true = just Stop
  ... | no _     | _        | _ = nothing
  ... | yes refl | no _     | _ = nothing
  ... | yes refl | yes refl | false with length txs ≟ length bm
  ...   | yes _ = just
        (Output ⦃ DecEq-TxsReply ⦄ (apiLPev l d lfpRecvBlockTxs) (q , zip bm txs)
           (Ret (inj₁ stIdle)))
  ...   | no _ = just Stop
  v (_ , receiveLFP _ _) _ = nothing
  v (_ , sendLFP _ _)    _ = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , doneLFP _ _)    _ = nothing
-- StDone: successful termination (√)
clientStepP _ _ stDone = Ret (inj₂ _)

-- the consumer peer: loop the step from the idle state
LFPclientStClient : Link → Dir → PTree LFPEv (ExtI LFPEv) Rr
LFPclientStClient l d = iter (clientStepP l d) stIdle

------------------------------------------------------------------------
-- Step 6: the server (producer) peer, with request reporting built in.
------------------------------------------------------------------------

-- one producer step.  REQUEST REPORTING IS BUILT IN (spec §2.4): the producer emits
-- `lfpReqBlockRequest ! q` / `lfpReqBlockTxsRequest ! (q , bm)` between the wire receive
-- and the busy state, so the application serves exactly what was asked for and no `…R`
-- variant of this peer is needed.  This is the `reqLFBlockRequest` idiom of `82ca4056`.
serverStepP : Link → Dir → LFPState → PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)
serverStepP l d stIdle = pchoice v
  where
  v : (at : AnyTypes LFPEv)
    → ContinueType at (Maybe (PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)))
  v (_ , receiveLFP l′ d′) (_ , _ , _ , leiosFetchP (MsgLFPBlockRequest q))
    with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (Output ⦃ DecEq-EBPoint ⦄ (apiLPev l d lfpReqBlockRequest) q
           (Ret (inj₁ stBlock)))
  ... | _        | _        = nothing
  -- Malformed offset lists are received, then stopped before the API report.
  v (_ , receiveLFP l′ d′) (_ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest q bm))
    with l′ ≟ l | d′ ≟ d | decodable bm
  ... | yes refl | yes refl | false = just Stop
  ... | yes refl | yes refl | true = just
        (Output ⦃ DecEq-TxsRequest ⦄ (apiLPev l d lfpReqBlockTxsRequest) (q , bm)
           (Ret (inj₁ (stBlockTxs q bm))))
  ... | _        | _        | _ = nothing
  v (_ , receiveLFP l′ d′) (_ , _ , _ , leiosFetchP MsgLFPDone) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (doneLFP l d ⟶₀ Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , receiveLFP _ _) _ = nothing
  v (_ , sendLFP _ _)    _ = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , doneLFP _ _)    _ = nothing
serverStepP l d stBlock = pchoice v
  where
  v : (at : AnyTypes LFPEv)
    → ContinueType at (Maybe (PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)))
  v (_ , apiLPev l′ d′ lfpSendBlock) eb with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLFP l d ! (time₀ , FromResponder , length₀ , leiosFetchP (MsgLFPBlock eb)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , sendLFP _ _)    _ = nothing
  v (_ , receiveLFP _ _) _ = nothing
  v (_ , doneLFP _ _)    _ = nothing
serverStepP l d (stBlockTxs q bm) = pchoice v
  where
  v : (at : AnyTypes LFPEv)
    → ContinueType at (Maybe (PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)))
  -- Carry the stored request for stage 3; the wire reply only contains API transactions.
  v (_ , apiLPev l′ d′ lfpSendBlockTxs) (q′ , es) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLFP l d !
           (time₀ , FromResponder , length₀ , leiosFetchP (MsgLFPBlockTxs (map proj₂ es))) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , sendLFP _ _)    _ = nothing
  v (_ , receiveLFP _ _) _ = nothing
  v (_ , doneLFP _ _)    _ = nothing
-- StDone: successful termination (√)
serverStepP _ _ stDone = Ret (inj₂ _)

-- the producer peer: loop the step from the idle state
LFPserverStClient : Link → Dir → PTree LFPEv (ExtI LFPEv) Rr
LFPserverStClient l d = iter (serverStepP l d) stIdle

------------------------------------------------------------------------
-- Step 7: network-fragment injection into `Net` (documentation stub).
------------------------------------------------------------------------

-- intended Net images of the prototype LeiosFetch wire events (api/done: none)
ιLFPNet : ∀ {A} → LFPEv A → Maybe (Net Payload A)
ιLFPNet (sendLFP l d)    = just (input  l d N2N_LeiosFetch)
ιLFPNet (receiveLFP l d) = just (output l d N2N_LeiosFetch)
ιLFPNet (apiLPev _ _ _)  = nothing
ιLFPNet (doneLFP _ _)    = nothing

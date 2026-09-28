{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the LEIOS-PROTOTYPE LeiosNotify peers.
--
-- Mirrors the other peer modules.  Role mapping (Ouroboros naming):
-- `clientStepP` = the CONSUMER (initiator: drives requests via api, runs
-- delivery handlers on receive); `serverStepP` = the PRODUCER (waits for the
-- request off the wire, chooses which notification to send via api).  Wire
-- events `sendLNP`/`receiveLNP` negotiate `Payload`; api/done are peer-local.
-- Productive via `iter` (no NON_TERMINATING).
--
-- This module models the Leios mini-protocol as implemented on the `leios-prototype`
-- branch of ouroboros-consensus (`LeiosDemoOnlyTest{Notify,Fetch}.hs`, protocol numbers
-- 18/19), which adapts the CIP-164 draft of July 2026.  Messages, payload types, state
-- machine and agency follow the prototype exactly, with two payload abstractions recorded
-- in the ADR `docs/superpowers/decisions/2026-09-21-leios-tx-closure-and-object-identities.md`
-- (`TxBitmap` is a concrete offset set; `MsgLeiosBlockTxs` is an offset-indexed map without
-- a bitmap echo); pipelining and credits, vote weights, deadlines, equivocation and
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

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.LeiosNotifyP (p : Params) where

open import Level renaming (zero to lzero)
import Data.Unit.Polymorphic as Poly
open import Data.Unit using (⊤)
open import Data.List using (List)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees

open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net  p

open Params p

------------------------------------------------------------------------
-- Step 1: the per-protocol event type `LNPEv`.
------------------------------------------------------------------------

-- the leios-prototype LeiosNotify peer alphabet
data LNPEv : Set → Set where
  sendLNP    : Link → Dir → LNPEv Payload   -- peer→net (→ input)
  receiveLNP : Link → Dir → LNPEv Payload   -- net→peer (→ output)
  apiLPev    : (l : Link) (d : Dir) (m : ApiLPTag) → LNPEv (ApiLPCar m)  -- peer-local
  doneLNP    : Link → Dir → LNPEv ⊤          -- peer-local: Done

------------------------------------------------------------------------
-- Step 2: decidable equality on `AnyTypes LNPEv`.
------------------------------------------------------------------------

-- decidable equality on existential-wrapped prototype LeiosNotify events
LNPEv-≟ : (x y : AnyTypes LNPEv) → Dec (x ≡ y)
LNPEv-≟ = go
  where
  go : (x y : AnyTypes LNPEv) → Dec (x ≡ y)
  go (_ , sendLNP l₁ d₁)     (_ , sendLNP l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , receiveLNP l₁ d₁)  (_ , receiveLNP l₂ d₂)  with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiLPev l₁ d₁ m₁) (_ , apiLPev l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneLNP l₁ d₁)     (_ , doneLNP l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendLNP _ _)    (_ , receiveLNP _ _) = no λ ()
  go (_ , sendLNP _ _)    (_ , apiLPev _ _ _)  = no λ ()
  go (_ , sendLNP _ _)    (_ , doneLNP _ _)    = no λ ()
  go (_ , receiveLNP _ _) (_ , sendLNP _ _)    = no λ ()
  go (_ , receiveLNP _ _) (_ , apiLPev _ _ _)  = no λ ()
  go (_ , receiveLNP _ _) (_ , doneLNP _ _)    = no λ ()
  go (_ , apiLPev _ _ _)  (_ , sendLNP _ _)    = no λ ()
  go (_ , apiLPev _ _ _)  (_ , receiveLNP _ _) = no λ ()
  go (_ , apiLPev _ _ _)  (_ , doneLNP _ _)    = no λ ()
  go (_ , doneLNP _ _)    (_ , sendLNP _ _)    = no λ ()
  go (_ , doneLNP _ _)    (_ , receiveLNP _ _) = no λ ()
  go (_ , doneLNP _ _)    (_ , apiLPev _ _ _)  = no λ ()

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

-- The `!`-output delivery-handler carriers that need a `DecEq` — `(EBHash × LSlot) × Size`
-- and `List VoteBlob` — are supplied EXPLICITLY at each `Output` site, from `Data.agda`'s
-- named instance terms (`DecEq-Offer`, `DecEq-EBPoint`) or the generic
-- `DecEqI.DecEq-List`.  A local named instance would both make the component of a `×`
-- carrier ambiguous during instance search (`LeiosFetch.agda:114-120`) and risk handing an
-- `Output` a different-but-equal term from the one a later proof expects.

import CSP.Operators {E = LNPEv} as LNPOps
open LNPOps LNPEv-≟

------------------------------------------------------------------------
-- Step 4: unified peer state (both peers walk the same FSM; agency differs).
------------------------------------------------------------------------

-- the leios-prototype LeiosNotify peer state; identical to the prototype's
-- `StIdle | StBusy | StDone`.  SPECIALISATION: depth-1, no pipelining (spec §3).
data LNPState : Set where
  stIdle : LNPState   -- consumer requests / producer awaits a request
  stBusy : LNPState   -- producer sends ONE notification / consumer awaits it
  stDone : LNPState   -- terminal (√)

instance
  -- decidable equality on the unified prototype LeiosNotify state
  DecEq-LNPState : DecEq LNPState
  DecEq-LNPState ._≟_ = go
    where
    go : (x y : LNPState) → Dec (x ≡ y)
    go stIdle stIdle = yes refl
    go stBusy stBusy = yes refl
    go stDone stDone = yes refl
    go stIdle stBusy = no λ ()
    go stIdle stDone = no λ ()
    go stBusy stIdle = no λ ()
    go stBusy stDone = no λ ()
    go stDone stIdle = no λ ()
    go stDone stBusy = no λ ()

------------------------------------------------------------------------
-- Step 5: the client (consumer) peer.
------------------------------------------------------------------------

-- one consumer step (the body of the `iter` loop)
clientStepP : Link → Dir → LNPState → PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)
clientStepP l d stIdle = pchoice v
  where
  v : (at : AnyTypes LNPEv)
    → ContinueType at (Maybe (PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)))
  v (_ , apiLPev l′ d′ lnpSendRequestNext) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLNP l d ! (time₀ , FromInitiator , length₀ , leiosNotifyP MsgLNPRequestNext) ⟶
           Ret (inj₁ stBusy))
  ... | _        | _        = nothing
  v (_ , apiLPev l′ d′ lnpSendDone) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLNP l d ! (time₀ , FromInitiator , length₀ , leiosNotifyP MsgLNPDone) ⟶
           Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , sendLNP _ _)    _ = nothing
  v (_ , receiveLNP _ _) _ = nothing
  v (_ , doneLNP _ _)    _ = nothing
clientStepP l d stBusy = pchoice v
  where
  v : (at : AnyTypes LNPEv)
    → ContinueType at (Maybe (PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)))
  v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP (MsgLNPBlockAnnouncement h))
    with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (apiLPev l d lnpRecvBlockAnnouncement ! h ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP (MsgLNPBlockOffer q sz))
    with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (Output ⦃ DecEq-Offer ⦄ (apiLPev l d lnpRecvBlockOffer) (q , sz)
           (Ret (inj₁ stIdle)))
  ... | _        | _        = nothing
  v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP (MsgLNPBlockTxsOffer q))
    with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (Output ⦃ DecEq-EBPoint ⦄ (apiLPev l d lnpRecvBlockTxsOffer) q
           (Ret (inj₁ stIdle)))
  ... | _        | _        = nothing
  v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP (MsgLNPVotes vs))
    with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (Output ⦃ DecEqI.DecEq-List ⦄ (apiLPev l d lnpRecvVotes) vs (Ret (inj₁ stIdle)))
  ... | _        | _        = nothing
  v (_ , receiveLNP _ _) _ = nothing
  v (_ , sendLNP _ _)    _ = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , doneLNP _ _)    _ = nothing
-- StDone: successful termination (√)
clientStepP _ _ stDone = Ret (inj₂ _)

-- the consumer peer: loop the step from the idle state
LNPclientStClient : Link → Dir → PTree LNPEv (ExtI LNPEv) Rr
LNPclientStClient l d = iter (clientStepP l d) stIdle

------------------------------------------------------------------------
-- Step 6: the server (producer) peer.
------------------------------------------------------------------------

-- one producer step: in `stBusy` the long-poll is answered with EXACTLY ONE
-- notification, chosen by whichever api event the application offers
serverStepP : Link → Dir → LNPState → PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)
serverStepP l d stIdle = pchoice v
  where
  v : (at : AnyTypes LNPEv)
    → ContinueType at (Maybe (PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)))
  v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP MsgLNPRequestNext) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Ret (inj₁ stBusy))
  ... | _        | _        = nothing
  v (_ , receiveLNP l′ d′) (_ , _ , _ , leiosNotifyP MsgLNPDone) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (doneLNP l d ⟶₀ Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , receiveLNP _ _) _ = nothing
  v (_ , sendLNP _ _)    _ = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , doneLNP _ _)    _ = nothing
serverStepP l d stBusy = pchoice v
  where
  v : (at : AnyTypes LNPEv)
    → ContinueType at (Maybe (PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)))
  v (_ , apiLPev l′ d′ lnpSendBlockAnnouncement) h with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLNP l d !
           (time₀ , FromResponder , length₀ , leiosNotifyP (MsgLNPBlockAnnouncement h)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLPev l′ d′ lnpSendBlockOffer) (q , sz) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLNP l d !
           (time₀ , FromResponder , length₀ , leiosNotifyP (MsgLNPBlockOffer q sz)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLPev l′ d′ lnpSendBlockTxsOffer) q with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLNP l d !
           (time₀ , FromResponder , length₀ , leiosNotifyP (MsgLNPBlockTxsOffer q)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLPev l′ d′ lnpSendVotes) vs with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLNP l d !
           (time₀ , FromResponder , length₀ , leiosNotifyP (MsgLNPVotes vs)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLPev _ _ _)  _ = nothing
  v (_ , sendLNP _ _)    _ = nothing
  v (_ , receiveLNP _ _) _ = nothing
  v (_ , doneLNP _ _)    _ = nothing
-- StDone: successful termination (√)
serverStepP _ _ stDone = Ret (inj₂ _)

-- the producer peer: loop the step from the idle state
LNPserverStClient : Link → Dir → PTree LNPEv (ExtI LNPEv) Rr
LNPserverStClient l d = iter (serverStepP l d) stIdle

------------------------------------------------------------------------
-- Step 7: network-fragment injection into `Net` (documentation stub).
------------------------------------------------------------------------

-- intended Net images of the prototype LeiosNotify wire events (api/done: none)
ιLNPNet : ∀ {A} → LNPEv A → Maybe (Net Payload A)
ιLNPNet (sendLNP l d)    = just (input  l d N2N_LeiosNotify)
ιLNPNet (receiveLNP l d) = just (output l d N2N_LeiosNotify)
ιLNPNet (apiLPev _ _ _)  = nothing
ιLNPNet (doneLNP _ _)    = nothing

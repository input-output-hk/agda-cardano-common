{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the LeiosFetch mini-protocol peers.
--
-- Mirrors the other peer modules.  Role mapping (Ouroboros naming):
-- `clientStep` = the CONSUMER (initiator: drives fetch requests via api,
-- runs delivery handlers on receive); `serverStep` = the PRODUCER (waits for
-- the request off the wire, delivers via api).  Wire events
-- `sendLF`/`receiveLF` negotiate `Payload`; api/done are peer-local.
-- Productive via `iter` (no NON_TERMINATING).
--
-- Protocol (old single-protocol LeiosFetch, ID 19): from `stIdle` the
-- consumer requests an EB (`MsgLFBlockRequest` → `stBlock`), selective txs
-- (`MsgLFBlockTxsRequest` → `stBlockTxs`), votes (`MsgLFVotesRequest` →
-- `stVotes`), or a block range (`MsgLFBlockRangeRequest` → `stBlockRange`),
-- or terminates (`MsgLFDone` → `stDone`).  The producer delivers in the
-- matching busy state, returning to `stIdle`.  The block-range case streams:
-- the producer may send several `MsgLFNextBlockAndTxsInRange` (staying in
-- `stBlockRange`) before a final `MsgLFLastBlockAndTxsInRange` returns to
-- `stIdle`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.LeiosFetch (p : Params) where

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
-- Step 1: the per-protocol event type `LFEv`.
------------------------------------------------------------------------

-- the LeiosFetch peer alphabet
data LFEv : Set → Set where
  sendLF    : Link → Dir → LFEv Payload   -- peer→net (→ input)
  receiveLF : Link → Dir → LFEv Payload   -- net→peer (→ output)
  apiLFev   : (l : Link) (d : Dir) (m : ApiLFTag) → LFEv (ApiLFCar m)  -- peer-local
  doneLF    : Link → Dir → LFEv ⊤          -- peer-local: Done

------------------------------------------------------------------------
-- Step 2: decidable equality on `AnyTypes LFEv`.
------------------------------------------------------------------------

-- decidable equality on existential-wrapped LeiosFetch events
LFEv-≟ : (x y : AnyTypes LFEv) → Dec (x ≡ y)
LFEv-≟ = go
  where
  go : (x y : AnyTypes LFEv) → Dec (x ≡ y)
  go (_ , sendLF l₁ d₁)     (_ , sendLF l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , receiveLF l₁ d₁)  (_ , receiveLF l₂ d₂)  with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiLFev l₁ d₁ m₁) (_ , apiLFev l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneLF l₁ d₁)     (_ , doneLF l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendLF _ _)    (_ , receiveLF _ _) = no λ ()
  go (_ , sendLF _ _)    (_ , apiLFev _ _ _) = no λ ()
  go (_ , sendLF _ _)    (_ , doneLF _ _)    = no λ ()
  go (_ , receiveLF _ _) (_ , sendLF _ _)    = no λ ()
  go (_ , receiveLF _ _) (_ , apiLFev _ _ _) = no λ ()
  go (_ , receiveLF _ _) (_ , doneLF _ _)    = no λ ()
  go (_ , apiLFev _ _ _) (_ , sendLF _ _)    = no λ ()
  go (_ , apiLFev _ _ _) (_ , receiveLF _ _) = no λ ()
  go (_ , apiLFev _ _ _) (_ , doneLF _ _)    = no λ ()
  go (_ , doneLF _ _)    (_ , sendLF _ _)    = no λ ()
  go (_ , doneLF _ _)    (_ , receiveLF _ _) = no λ ()
  go (_ , doneLF _ _)    (_ , apiLFev _ _ _) = no λ ()

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

-- The `!`-output delivery-handler carriers (`List Tx` / `List VoteBlob` /
-- `Block × List Tx`) need `DecEq`.  They are supplied explicitly at each
-- `Output` site via the generic `DecEqI.DecEq-List` / `DecEqI.DecEq-×`
-- (whose element/component `DecEq`s — `DecEq-Tx`, `decVoteBlob`, `decBlock` —
-- are ambient), rather than as named local instances: a local `DecEq (List
-- Tx)` instance would make the `List Tx` component of the `×` carrier
-- ambiguous against the generic during instance search.

import CSP.Operators {E = LFEv} as LFOps
open LFOps LFEv-≟

------------------------------------------------------------------------
-- Step 4: unified peer state (both peers walk the same FSM; agency differs).
------------------------------------------------------------------------

-- LeiosFetch peer state
data LFState : Set where
  stIdle       : LFState   -- consumer requests / producer awaits a request
  stBlock      : LFState   -- EB delivery outstanding
  stBlockTxs   : LFState   -- tx delivery outstanding
  stVotes      : LFState   -- vote delivery outstanding
  stBlockRange : LFState   -- block-range streaming (self-loop until Last)
  stDone       : LFState   -- terminal (√)

instance
  -- decidable equality on the unified LeiosFetch state
  DecEq-LFState : DecEq LFState
  DecEq-LFState ._≟_ = go
    where
    go : (x y : LFState) → Dec (x ≡ y)
    go stIdle       stIdle       = yes refl
    go stBlock      stBlock      = yes refl
    go stBlockTxs   stBlockTxs   = yes refl
    go stVotes      stVotes      = yes refl
    go stBlockRange stBlockRange = yes refl
    go stDone       stDone       = yes refl
    go stIdle       stBlock      = no λ ()
    go stIdle       stBlockTxs   = no λ ()
    go stIdle       stVotes      = no λ ()
    go stIdle       stBlockRange = no λ ()
    go stIdle       stDone       = no λ ()
    go stBlock      stIdle       = no λ ()
    go stBlock      stBlockTxs   = no λ ()
    go stBlock      stVotes      = no λ ()
    go stBlock      stBlockRange = no λ ()
    go stBlock      stDone       = no λ ()
    go stBlockTxs   stIdle       = no λ ()
    go stBlockTxs   stBlock      = no λ ()
    go stBlockTxs   stVotes      = no λ ()
    go stBlockTxs   stBlockRange = no λ ()
    go stBlockTxs   stDone       = no λ ()
    go stVotes      stIdle       = no λ ()
    go stVotes      stBlock      = no λ ()
    go stVotes      stBlockTxs   = no λ ()
    go stVotes      stBlockRange = no λ ()
    go stVotes      stDone       = no λ ()
    go stBlockRange stIdle       = no λ ()
    go stBlockRange stBlock      = no λ ()
    go stBlockRange stBlockTxs   = no λ ()
    go stBlockRange stVotes      = no λ ()
    go stBlockRange stDone       = no λ ()
    go stDone       stIdle       = no λ ()
    go stDone       stBlock      = no λ ()
    go stDone       stBlockTxs   = no λ ()
    go stDone       stVotes      = no λ ()
    go stDone       stBlockRange = no λ ()

------------------------------------------------------------------------
-- Step 5: the client (consumer) peer.
------------------------------------------------------------------------

-- one consumer step (the body of the `iter` loop)
clientStep : Link → Dir → LFState → PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)
clientStep l d stIdle = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , apiLFev l′ d′ sendLFBlockRequest) pt with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ⟶
           Ret (inj₁ stBlock))
  ... | _        | _        = nothing
  v (_ , apiLFev l′ d′ sendLFBlockTxsRequest) (pt , bm) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ⟶
           Ret (inj₁ stBlockTxs))
  ... | _        | _        = nothing
  v (_ , apiLFev l′ d′ sendLFVotesRequest) vs with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ⟶
           Ret (inj₁ stVotes))
  ... | _        | _        = nothing
  v (_ , apiLFev l′ d′ sendLFBlockRangeRequest) r with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ⟶
           Ret (inj₁ stBlockRange))
  ... | _        | _        = nothing
  v (_ , apiLFev l′ d′ sendLFDone) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) ⟶
           (doneLF l d ⟶₀ Ret (inj₁ stDone)))
  ... | _        | _        = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
clientStep l d stBlock = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch (MsgLFBlock b)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiLFev l d recvLFBlock ! b ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
clientStep l d stBlockTxs = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch (MsgLFBlockTxs ts)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Output ⦃ DecEqI.DecEq-List ⦄ (apiLFev l d recvLFBlockTxs) ts (Ret (inj₁ stIdle)))
  ... | _        | _        = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
clientStep l d stVotes = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch (MsgLFVoteDelivery vs)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Output ⦃ DecEqI.DecEq-List ⦄ (apiLFev l d recvLFVoteDelivery) vs (Ret (inj₁ stIdle)))
  ... | _        | _        = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
clientStep l d stBlockRange = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Output ⦃ DecEqI.DecEq-× ⦄ (apiLFev l d recvLFRangeBlock) (b , ts) (Ret (inj₁ stBlockRange)))
  ... | _        | _        = nothing
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Output ⦃ DecEqI.DecEq-× ⦄ (apiLFev l d recvLFRangeBlock) (b , ts) (Ret (inj₁ stIdle)))
  ... | _        | _        = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
-- StDone: successful termination (√)
clientStep _ _ stDone = Ret (inj₂ _)

-- the consumer peer: loop the step from the idle state
LFclientStClient : Link → Dir → PTree LFEv (ExtI LFEv) Rr
LFclientStClient l d = iter (clientStep l d) stIdle

------------------------------------------------------------------------
-- Step 6: the server (producer) peer.
------------------------------------------------------------------------

-- one producer step (the body of the `iter` loop)
serverStep : Link → Dir → LFState → PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)
serverStep l d stIdle = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch (MsgLFBlockRequest pt)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Ret (inj₁ stBlock))
  ... | _        | _        = nothing
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch (MsgLFBlockTxsRequest pt bm)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Ret (inj₁ stBlockTxs))
  ... | _        | _        = nothing
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch (MsgLFVotesRequest vs)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Ret (inj₁ stVotes))
  ... | _        | _        = nothing
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch (MsgLFBlockRangeRequest r)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Ret (inj₁ stBlockRange))
  ... | _        | _        = nothing
  v (_ , receiveLF l′ d′) (_ , _ , _ , leiosFetch MsgLFDone) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (doneLF l d ⟶₀ Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
serverStep l d stBlock = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , apiLFev l′ d′ sendLFBlock) b with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
serverStep l d stBlockTxs = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , apiLFev l′ d′ sendLFBlockTxs) ts with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
serverStep l d stVotes = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , apiLFev l′ d′ sendLFVoteDelivery) vs with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
serverStep l d stBlockRange = pchoice v
  where
  v : (at : AnyTypes LFEv)
    → ContinueType at (Maybe (PTree LFEv (ExtI LFEv) (LFState ⊎ Rr)))
  v (_ , apiLFev l′ d′ sendLFNextBlockAndTxsInRange) (b , ts) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ⟶
           Ret (inj₁ stBlockRange))
  ... | _        | _        = nothing
  v (_ , apiLFev l′ d′ sendLFLastBlockAndTxsInRange) (b , ts) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLF l d ! (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLFev _ _ _) _ = nothing
  v (_ , sendLF _ _)    _ = nothing
  v (_ , receiveLF _ _) _ = nothing
  v (_ , doneLF _ _)    _ = nothing
-- StDone: successful termination (√)
serverStep _ _ stDone = Ret (inj₂ _)

-- the producer peer: loop the step from the idle state
LFserverStClient : Link → Dir → PTree LFEv (ExtI LFEv) Rr
LFserverStClient l d = iter (serverStep l d) stIdle

------------------------------------------------------------------------
-- Step 7: network-fragment injection into `Net` (documentation stub).
------------------------------------------------------------------------

-- intended Net images of the LeiosFetch wire events (api/done: none)
ιLFNet : ∀ {A} → LFEv A → Maybe (Net Payload A)
ιLFNet (sendLF l d)    = just (input  l d N2N_LeiosFetch)
ιLFNet (receiveLF l d) = just (output l d N2N_LeiosFetch)
ιLFNet (apiLFev _ _ _) = nothing
ιLFNet (doneLF _ _)    = nothing

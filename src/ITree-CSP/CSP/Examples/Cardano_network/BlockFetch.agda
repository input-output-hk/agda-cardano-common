{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the BlockFetch mini-protocol peers.
--
-- The BlockFetch peers are written over their own small event type
-- `BFEv`, then (at the composition step, `BlockFetchNetworkPar`) renamed
-- into the shared network alphabet `Net_Api Payload`.  This mirrors
-- `KeepAlive.agda`: wire events `sendBF`/`receiveBF` negotiate `Payload`;
-- the application-facing api/done events are peer-local and hidden before
-- any rename.  Both peers are productive (no NON_TERMINATING): each is a
-- non-recursive step function tied with `iter`.
--
-- Protocol: the client requests a block range; the server streams blocks.
--   Client stIdle     : api RequestRange ⇒ send MsgRequestRange ⇒ stBusy
--                     | api ClientDone  ⇒ send MsgClientDone   ⇒ stDone
--          stBusy    : recv MsgStartBatch ⇒ stStreaming | recv MsgNoBlocks ⇒ stIdle
--          stStreaming: recv MsgBlock b ⇒ deliver (recvBFBlock b) ⇒ stStreaming
--                     | recv MsgBatchDone ⇒ stIdle
--   Server stIdle     : recv MsgRequestRange r ⇒ notify (reqBFRange r) ⇒ stBusy
--                     | recv MsgClientDone ⇒ stDone
--          stBusy    : api StartBatch ⇒ send MsgStartBatch ⇒ stStreaming
--                     | api NoBlocks  ⇒ send MsgNoBlocks   ⇒ stIdle
--          stStreaming: api Block b ⇒ send MsgBlock b ⇒ stStreaming
--                     | api BatchDone ⇒ send MsgBatchDone ⇒ stIdle
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.BlockFetch (p : Params) where

open import Level renaming (zero to lzero)
import Data.Unit.Polymorphic as Poly
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net  p

open Params p

------------------------------------------------------------------------
-- Step 1: the per-protocol event type `BFEv`.
--
-- Network events negotiate `Payload`; the application-facing api/done
-- events are peer-local (`apiBFev` carries `ApiBFCar m`; `doneBF` is `⊤`).
------------------------------------------------------------------------

-- the BlockFetch peer alphabet
data BFEv : Set → Set where
  sendBF    : Conn N2N_BlockFetch → BFEv Payload   -- peer→net (→ input);  emitted via !
  receiveBF : Conn N2N_BlockFetch → BFEv Payload   -- net→peer (→ output); bound via ?
  apiBFev   : (c : Conn N2N_BlockFetch) (m : ApiBFTag) → BFEv (ApiBFCar m)  -- peer-local
  doneBF    : Conn N2N_BlockFetch → BFEv ⊤          -- peer-local: Done

------------------------------------------------------------------------
-- Step 2: decidable equality on `AnyTypes BFEv`.
------------------------------------------------------------------------

-- decidable equality on existential-wrapped BlockFetch events
BFEv-≟ : (x y : AnyTypes BFEv) → Dec (x ≡ y)
BFEv-≟ = go
  where
  go : (x y : AnyTypes BFEv) → Dec (x ≡ y)
  go (_ , sendBF c₁)     (_ , sendBF c₂)     with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , receiveBF c₁)  (_ , receiveBF c₂)  with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiBFev c₁ m₁) (_ , apiBFev c₂ m₂) with c₁ ≟ c₂ | m₁ ≟ m₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneBF c₁)     (_ , doneBF c₂)     with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendBF _)    (_ , receiveBF _) = no λ ()
  go (_ , sendBF _)    (_ , apiBFev _ _) = no λ ()
  go (_ , sendBF _)    (_ , doneBF _)    = no λ ()
  go (_ , receiveBF _) (_ , sendBF _)    = no λ ()
  go (_ , receiveBF _) (_ , apiBFev _ _) = no λ ()
  go (_ , receiveBF _) (_ , doneBF _)    = no λ ()
  go (_ , apiBFev _ _) (_ , sendBF _)    = no λ ()
  go (_ , apiBFev _ _) (_ , receiveBF _) = no λ ()
  go (_ , apiBFev _ _) (_ , doneBF _)    = no λ ()
  go (_ , doneBF _)    (_ , sendBF _)    = no λ ()
  go (_ , doneBF _)    (_ , receiveBF _) = no λ ()
  go (_ , doneBF _)    (_ , apiBFev _ _) = no λ ()

------------------------------------------------------------------------
-- Step 3: peer return type and its DecEq.
------------------------------------------------------------------------

-- the peers return the unit on √
Rr : Set
Rr = Poly.⊤ {lzero}

instance
  -- trivial decidable equality on the unit return type
  DecEq-Rr : DecEq Rr
  DecEq-Rr = record { _≟_ = λ _ _ → yes refl }

------------------------------------------------------------------------
-- CSP operators over the small BlockFetch alphabet.
------------------------------------------------------------------------

import CSP.Operators {E = BFEv} as BFOps
open BFOps BFEv-≟

------------------------------------------------------------------------
-- Step 4: the client (initiator) peer.
------------------------------------------------------------------------

-- unified BlockFetch peer state (both peers walk the same FSM; agency differs).
data BFState : Set where
  stIdle      : BFState   -- Idle: client offers the api / server awaits a request
  stBusy      : BFState   -- Busy: awaiting StartBatch / NoBlocks (client) or offering it (server)
  stStreaming : BFState   -- Streaming: the block batch
  stDone      : BFState   -- terminal (√)

instance
  -- decidable equality on the unified BlockFetch state
  DecEq-BFState : DecEq BFState
  DecEq-BFState ._≟_ = go
    where
    go : (x y : BFState) → Dec (x ≡ y)
    go stIdle      stIdle      = yes refl
    go stBusy      stBusy      = yes refl
    go stStreaming stStreaming = yes refl
    go stDone      stDone      = yes refl
    go stIdle      stBusy      = no λ ()
    go stIdle      stStreaming = no λ ()
    go stIdle      stDone      = no λ ()
    go stBusy      stIdle      = no λ ()
    go stBusy      stStreaming = no λ ()
    go stBusy      stDone      = no λ ()
    go stStreaming stIdle      = no λ ()
    go stStreaming stBusy      = no λ ()
    go stStreaming stDone      = no λ ()
    go stDone      stIdle      = no λ ()
    go stDone      stBusy      = no λ ()
    go stDone      stStreaming = no λ ()

-- one client step (the body of the `iter` loop)
clientStep : Conn N2N_BlockFetch → BFState → PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)
clientStep c stIdle = pchoice v
  where
  v : (at : AnyTypes BFEv)
    → ContinueType at (Maybe (PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)))
  v (_ , apiBFev c′ sendBFRequestRange) range with c′ ≟ c
  ... | yes refl = just
        (sendBF c ! (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange range)) ⟶
           Ret (inj₁ stBusy))
  ... | no _     = nothing
  v (_ , apiBFev c′ sendBFClientDone) _ with c′ ≟ c
  ... | yes refl = just
        (sendBF c ! (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ⟶
           (doneBF c ⟶₀ Ret (inj₁ stDone)))
  ... | no _     = nothing
  v (_ , apiBFev _ _) _ = nothing
  v (_ , sendBF _)    _ = nothing
  v (_ , receiveBF _) _ = nothing
  v (_ , doneBF _)    _ = nothing
clientStep c stBusy = pchoice v
  where
  v : (at : AnyTypes BFEv)
    → ContinueType at (Maybe (PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)))
  v (_ , receiveBF c′) (_ , _ , _ , blockFetch MsgStartBatch) with c′ ≟ c
  ... | yes refl = just (Ret (inj₁ stStreaming))
  ... | no _     = nothing
  v (_ , receiveBF c′) (_ , _ , _ , blockFetch MsgNoBlocks) with c′ ≟ c
  ... | yes refl = just (Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , receiveBF _) _ = nothing
  v (_ , sendBF _)    _ = nothing
  v (_ , apiBFev _ _) _ = nothing
  v (_ , doneBF _)    _ = nothing
clientStep c stStreaming = pchoice v
  where
  v : (at : AnyTypes BFEv)
    → ContinueType at (Maybe (PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)))
  v (_ , receiveBF c′) (_ , _ , _ , blockFetch (MsgBlock b)) with c′ ≟ c
  ... | yes refl = just (apiBFev c recvBFBlock ! b ⟶ Ret (inj₁ stStreaming))
  ... | no _     = nothing
  v (_ , receiveBF c′) (_ , _ , _ , blockFetch MsgBatchDone) with c′ ≟ c
  ... | yes refl = just (Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , receiveBF _) _ = nothing
  v (_ , sendBF _)    _ = nothing
  v (_ , apiBFev _ _) _ = nothing
  v (_ , doneBF _)    _ = nothing
-- Done: successful termination (√)
clientStep _ stDone = Ret (inj₂ _)

-- the client peer: loop the step from the idle state
BFclientStClient : Conn N2N_BlockFetch → PTree BFEv (ExtI BFEv) Rr
BFclientStClient c = iter (clientStep c) stIdle

------------------------------------------------------------------------
-- Step 5: the server (responder) peer — application-driven.
------------------------------------------------------------------------

-- one server step (the body of the `iter` loop)
serverStep : Conn N2N_BlockFetch → BFState → PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)
serverStep c stIdle = pchoice v
  where
  v : (at : AnyTypes BFEv)
    → ContinueType at (Maybe (PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)))
  v (_ , receiveBF c′) (_ , _ , _ , blockFetch (MsgRequestRange range)) with c′ ≟ c
  ... | yes refl = just (apiBFev c reqBFRange ! range ⟶ Ret (inj₁ stBusy))
  ... | no _     = nothing
  v (_ , receiveBF c′) (_ , _ , _ , blockFetch MsgClientDone) with c′ ≟ c
  ... | yes refl = just (doneBF c ⟶₀ Ret (inj₁ stDone))
  ... | no _     = nothing
  v (_ , receiveBF _) _ = nothing
  v (_ , sendBF _)    _ = nothing
  v (_ , apiBFev _ _) _ = nothing
  v (_ , doneBF _)    _ = nothing
serverStep c stBusy = pchoice v
  where
  v : (at : AnyTypes BFEv)
    → ContinueType at (Maybe (PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)))
  v (_ , apiBFev c′ sendBFStartBatch) _ with c′ ≟ c
  ... | yes refl = just
        (sendBF c ! (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ⟶
           Ret (inj₁ stStreaming))
  ... | no _     = nothing
  v (_ , apiBFev c′ sendBFNoBlocks) _ with c′ ≟ c
  ... | yes refl = just
        (sendBF c ! (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ⟶
           Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , apiBFev _ _) _ = nothing
  v (_ , sendBF _)    _ = nothing
  v (_ , receiveBF _) _ = nothing
  v (_ , doneBF _)    _ = nothing
serverStep c stStreaming = pchoice v
  where
  v : (at : AnyTypes BFEv)
    → ContinueType at (Maybe (PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)))
  v (_ , apiBFev c′ sendBFBlock) b with c′ ≟ c
  ... | yes refl = just
        (sendBF c ! (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ⟶
           Ret (inj₁ stStreaming))
  ... | no _     = nothing
  v (_ , apiBFev c′ sendBFBatchDone) _ with c′ ≟ c
  ... | yes refl = just
        (sendBF c ! (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ⟶
           Ret (inj₁ stIdle))
  ... | no _     = nothing
  v (_ , apiBFev _ _) _ = nothing
  v (_ , sendBF _)    _ = nothing
  v (_ , receiveBF _) _ = nothing
  v (_ , doneBF _)    _ = nothing
-- Done: successful termination (√)
serverStep _ stDone = Ret (inj₂ _)

-- the server peer: loop the step from the idle state
BFserverStClient : Conn N2N_BlockFetch → PTree BFEv (ExtI BFEv) Rr
BFserverStClient c = iter (serverStep c) stIdle

------------------------------------------------------------------------
-- Step 6: network-fragment injection into `Net` (documentation stub).
--
-- As for KeepAlive, a *total* `ι : BFEv A → Net Payload A` is impossible
-- while api/done have no `Net` image.  This `Maybe`-valued helper records
-- the intended images of the *network* events only; api/done are `nothing`
-- (peer-local, hidden before any real rename).  The total `ι` and the
-- `renameMap`/`Par` composition are built in `BlockFetchNetworkPar`.
------------------------------------------------------------------------

-- intended Net images of the BlockFetch wire events (api/done: none)
ιBFNet : ∀ {A} → BFEv A → Maybe (Net Payload A)
ιBFNet (sendBF c)    = just (input  N2N_BlockFetch c)
ιBFNet (receiveBF c) = just (output N2N_BlockFetch c)
ιBFNet (apiBFev _ _) = nothing
ιBFNet (doneBF _)    = nothing

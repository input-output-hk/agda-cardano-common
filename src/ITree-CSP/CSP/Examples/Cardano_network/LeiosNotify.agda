{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the LeiosNotify mini-protocol peers.
--
-- Mirrors the other peer modules.  Role mapping (Ouroboros naming):
-- `clientStep` = the CONSUMER (initiator: drives requests via api, runs
-- delivery handlers on receive); `serverStep` = the PRODUCER (waits for the
-- request off the wire, chooses which notification to send via api).  Wire
-- events `sendLN`/`receiveLN` negotiate `Payload`; api/done are peer-local.
-- Productive via `iter` (no NON_TERMINATING).
--
-- Protocol (old single-protocol LeiosNotify, ID 18): from `stIdle` the
-- consumer requests the next notification (`MsgLNRequestNext` → `stBusy`) or
-- terminates (`MsgLNDone` → `stDone`); in `stBusy` the producer replies with
-- exactly one of the four notifications, returning to `stIdle`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.LeiosNotify (p : Params) where

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
-- Step 1: the per-protocol event type `LNEv`.
------------------------------------------------------------------------

-- the LeiosNotify peer alphabet
data LNEv : Set → Set where
  sendLN    : Link → Dir → LNEv Payload   -- peer→net (→ input)
  receiveLN : Link → Dir → LNEv Payload   -- net→peer (→ output)
  apiLNev   : (l : Link) (d : Dir) (m : ApiLNTag) → LNEv (ApiLNCar m)  -- peer-local
  doneLN    : Link → Dir → LNEv ⊤          -- peer-local: Done

------------------------------------------------------------------------
-- Step 2: decidable equality on `AnyTypes LNEv`.
------------------------------------------------------------------------

-- decidable equality on existential-wrapped LeiosNotify events
LNEv-≟ : (x y : AnyTypes LNEv) → Dec (x ≡ y)
LNEv-≟ = go
  where
  go : (x y : AnyTypes LNEv) → Dec (x ≡ y)
  go (_ , sendLN l₁ d₁)     (_ , sendLN l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , receiveLN l₁ d₁)  (_ , receiveLN l₂ d₂)  with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiLNev l₁ d₁ m₁) (_ , apiLNev l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneLN l₁ d₁)     (_ , doneLN l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendLN _ _)    (_ , receiveLN _ _) = no λ ()
  go (_ , sendLN _ _)    (_ , apiLNev _ _ _) = no λ ()
  go (_ , sendLN _ _)    (_ , doneLN _ _)    = no λ ()
  go (_ , receiveLN _ _) (_ , sendLN _ _)    = no λ ()
  go (_ , receiveLN _ _) (_ , apiLNev _ _ _) = no λ ()
  go (_ , receiveLN _ _) (_ , doneLN _ _)    = no λ ()
  go (_ , apiLNev _ _ _) (_ , sendLN _ _)    = no λ ()
  go (_ , apiLNev _ _ _) (_ , receiveLN _ _) = no λ ()
  go (_ , apiLNev _ _ _) (_ , doneLN _ _)    = no λ ()
  go (_ , doneLN _ _)    (_ , sendLN _ _)    = no λ ()
  go (_ , doneLN _ _)    (_ , receiveLN _ _) = no λ ()
  go (_ , doneLN _ _)    (_ , apiLNev _ _ _) = no λ ()

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

  -- `!`-output carrier needing DecEq (the `List Vote` votes-offer handler;
  -- the ℕ/List instances are not re-exported through Data's using-import).
  DecEq-ListVote : DecEq (List Vote)
  DecEq-ListVote = DecEqI.DecEq-List

import CSP.Operators {E = LNEv} as LNOps
open LNOps LNEv-≟

------------------------------------------------------------------------
-- Step 4: unified peer state (both peers walk the same FSM; agency differs).
------------------------------------------------------------------------

-- LeiosNotify peer state
data LNState : Set where
  stIdle : LNState   -- consumer requests / producer awaits a request
  stBusy : LNState   -- producer sends one notification / consumer awaits it
  stDone : LNState   -- terminal (√)

instance
  -- decidable equality on the unified LeiosNotify state
  DecEq-LNState : DecEq LNState
  DecEq-LNState ._≟_ = go
    where
    go : (x y : LNState) → Dec (x ≡ y)
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
clientStep : Link → Dir → LNState → PTree LNEv (ExtI LNEv) (LNState ⊎ Rr)
clientStep l d stIdle = pchoice v
  where
  v : (at : AnyTypes LNEv)
    → ContinueType at (Maybe (PTree LNEv (ExtI LNEv) (LNState ⊎ Rr)))
  v (_ , apiLNev l′ d′ sendLNRequestNext) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLN l d ! (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ⟶
           Ret (inj₁ stBusy))
  ... | _        | _        = nothing
  v (_ , apiLNev l′ d′ sendLNDone) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLN l d ! (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ⟶
           (doneLN l d ⟶₀ Ret (inj₁ stDone)))
  ... | _        | _        = nothing
  v (_ , apiLNev _ _ _) _ = nothing
  v (_ , sendLN _ _)    _ = nothing
  v (_ , receiveLN _ _) _ = nothing
  v (_ , doneLN _ _)    _ = nothing
clientStep l d stBusy = pchoice v
  where
  v : (at : AnyTypes LNEv)
    → ContinueType at (Maybe (PTree LNEv (ExtI LNEv) (LNState ⊎ Rr)))
  v (_ , receiveLN l′ d′) (_ , _ , _ , leiosNotify (MsgLNBlockAnnouncement h)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiLNev l d recvLNBlockAnnouncement ! h ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveLN l′ d′) (_ , _ , _ , leiosNotify (MsgLNBlockOffer q)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiLNev l d recvLNBlockOffer ! q ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveLN l′ d′) (_ , _ , _ , leiosNotify (MsgLNBlockTxsOffer q)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiLNev l d recvLNBlockTxsOffer ! q ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveLN l′ d′) (_ , _ , _ , leiosNotify (MsgLNVotesOffer vs)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Output ⦃ DecEq-ListVote ⦄ (apiLNev l d recvLNVotesOffer) vs (Ret (inj₁ stIdle)))
  ... | _        | _        = nothing
  v (_ , receiveLN _ _) _ = nothing
  v (_ , sendLN _ _)    _ = nothing
  v (_ , apiLNev _ _ _) _ = nothing
  v (_ , doneLN _ _)    _ = nothing
-- StDone: successful termination (√)
clientStep _ _ stDone = Ret (inj₂ _)

-- the consumer peer: loop the step from the idle state
LNclientStClient : Link → Dir → PTree LNEv (ExtI LNEv) Rr
LNclientStClient l d = iter (clientStep l d) stIdle

------------------------------------------------------------------------
-- Step 6: the server (producer) peer.
------------------------------------------------------------------------

-- one producer step (the body of the `iter` loop)
serverStep : Link → Dir → LNState → PTree LNEv (ExtI LNEv) (LNState ⊎ Rr)
serverStep l d stIdle = pchoice v
  where
  v : (at : AnyTypes LNEv)
    → ContinueType at (Maybe (PTree LNEv (ExtI LNEv) (LNState ⊎ Rr)))
  v (_ , receiveLN l′ d′) (_ , _ , _ , leiosNotify MsgLNRequestNext) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Ret (inj₁ stBusy))
  ... | _        | _        = nothing
  v (_ , receiveLN l′ d′) (_ , _ , _ , leiosNotify MsgLNDone) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (doneLN l d ⟶₀ Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , receiveLN _ _) _ = nothing
  v (_ , sendLN _ _)    _ = nothing
  v (_ , apiLNev _ _ _) _ = nothing
  v (_ , doneLN _ _)    _ = nothing
serverStep l d stBusy = pchoice v
  where
  v : (at : AnyTypes LNEv)
    → ContinueType at (Maybe (PTree LNEv (ExtI LNEv) (LNState ⊎ Rr)))
  v (_ , apiLNev l′ d′ sendLNBlockAnnouncement) h with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLN l d ! (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLNev l′ d′ sendLNBlockOffer) q with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLN l d ! (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLNev l′ d′ sendLNBlockTxsOffer) q with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLN l d ! (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLNev l′ d′ sendLNVotesOffer) vs with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendLN l d ! (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiLNev _ _ _) _ = nothing
  v (_ , sendLN _ _)    _ = nothing
  v (_ , receiveLN _ _) _ = nothing
  v (_ , doneLN _ _)    _ = nothing
-- StDone: successful termination (√)
serverStep _ _ stDone = Ret (inj₂ _)

-- the producer peer: loop the step from the idle state
LNserverStClient : Link → Dir → PTree LNEv (ExtI LNEv) Rr
LNserverStClient l d = iter (serverStep l d) stIdle

------------------------------------------------------------------------
-- Step 7: network-fragment injection into `Net` (documentation stub).
------------------------------------------------------------------------

-- intended Net images of the LeiosNotify wire events (api/done: none)
ιLNNet : ∀ {A} → LNEv A → Maybe (Net Payload A)
ιLNNet (sendLN l d)    = just (input  l d N2N_LeiosNotify)
ιLNNet (receiveLN l d) = just (output l d N2N_LeiosNotify)
ιLNNet (apiLNev _ _ _) = nothing
ιLNNet (doneLN _ _)    = nothing

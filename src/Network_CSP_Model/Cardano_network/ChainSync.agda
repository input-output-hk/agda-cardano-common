{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the ChainSync mini-protocol peers.
--
-- Written over the small event type `CSEv`, then (in `ChainSyncNetworkPar`)
-- renamed into the shared `Net_Api Payload` alphabet.  Mirrors
-- `BlockFetch.agda`.  Wire events `sendCS`/`receiveCS` negotiate `Payload`;
-- api/done events are peer-local.  Both peers are productive (`iter`, no
-- NON_TERMINATING).
--
-- Protocol (consumer tracks producer's chain):
--   Client stIdle     : api RequestNext        ⇒ send MsgCSRequestNext   ⇒ stCanAwait
--                      | api FindIntersect pts  ⇒ send MsgCSFindIntersect ⇒ stIntersect
--                      | api Done               ⇒ send MsgCSDone          ⇒ stDone
--          stCanAwait : recv RollForward h t  ⇒ deliver recvCSRollforward ⇒ stIdle
--                      | recv RollBackward p t ⇒ deliver recvCSRollback    ⇒ stIdle
--                      | recv AwaitReply        ⇒ stMustReply
--          stMustReply: recv RollForward/RollBackward ⇒ deliver ⇒ stIdle
--          stIntersect: recv IntersectFound p t ⇒ deliver recvCSIntersectFound ⇒ stIdle
--                      | recv IntersectNotFound t ⇒ deliver recvCSIntersectNotFound ⇒ stIdle
--   Server stIdle     : recv RequestNext        ⇒ notify reqCSRequestNext   ⇒ stCanAwait
--                      | recv FindIntersect pts  ⇒ notify reqCSFindIntersect ⇒ stIntersect
--                      | recv Done               ⇒ stDone
--          stCanAwait : api RollForward/RollBackward ⇒ send ⇒ stIdle
--                      | api AwaitReply ⇒ send MsgCSAwaitReply ⇒ stMustReply
--          stMustReply: api RollForward/RollBackward ⇒ send ⇒ stIdle
--          stIntersect: api IntersectFound/IntersectNotFound ⇒ send ⇒ stIdle
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.ChainSync (p : Params) where

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
-- Step 1: the per-protocol event type `CSEv`.
------------------------------------------------------------------------

-- the ChainSync peer alphabet
data CSEv : Set → Set where
  sendCS    : Link → Dir → CSEv Payload   -- peer→net (→ input)
  receiveCS : Link → Dir → CSEv Payload   -- net→peer (→ output)
  apiCSev   : (l : Link) (d : Dir) (m : ApiCSTag) → CSEv (ApiCSCar m)  -- peer-local
  doneCS    : Link → Dir → CSEv ⊤          -- peer-local: Done

------------------------------------------------------------------------
-- Step 2: decidable equality on `AnyTypes CSEv`.
------------------------------------------------------------------------

-- decidable equality on existential-wrapped ChainSync events
CSEv-≟ : (x y : AnyTypes CSEv) → Dec (x ≡ y)
CSEv-≟ = go
  where
  go : (x y : AnyTypes CSEv) → Dec (x ≡ y)
  go (_ , sendCS l₁ d₁)     (_ , sendCS l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , receiveCS l₁ d₁)  (_ , receiveCS l₂ d₂)  with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiCSev l₁ d₁ m₁) (_ , apiCSev l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneCS l₁ d₁)     (_ , doneCS l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendCS _ _)    (_ , receiveCS _ _) = no λ ()
  go (_ , sendCS _ _)    (_ , apiCSev _ _ _) = no λ ()
  go (_ , sendCS _ _)    (_ , doneCS _ _)    = no λ ()
  go (_ , receiveCS _ _) (_ , sendCS _ _)    = no λ ()
  go (_ , receiveCS _ _) (_ , apiCSev _ _ _) = no λ ()
  go (_ , receiveCS _ _) (_ , doneCS _ _)    = no λ ()
  go (_ , apiCSev _ _ _) (_ , sendCS _ _)    = no λ ()
  go (_ , apiCSev _ _ _) (_ , receiveCS _ _) = no λ ()
  go (_ , apiCSev _ _ _) (_ , doneCS _ _)    = no λ ()
  go (_ , doneCS _ _)    (_ , sendCS _ _)    = no λ ()
  go (_ , doneCS _ _)    (_ , receiveCS _ _) = no λ ()
  go (_ , doneCS _ _)    (_ , apiCSev _ _ _) = no λ ()

------------------------------------------------------------------------
-- Step 3: peer return type, its DecEq, and carrier DecEq instances.
------------------------------------------------------------------------

-- the peers return the unit on √
Rr : Set
Rr = Poly.⊤ {lzero}

instance
  -- trivial decidable equality on the unit return type
  DecEq-Rr : DecEq Rr
  DecEq-Rr = record { _≟_ = λ _ _ → yes refl }

  -- `!`-output carriers needing DecEq (DecEq-× is not an instance; the
  -- List instance is not re-exported through `Data`'s using-import).
  DecEq-Header×Tip : DecEq (Header × Tip)
  DecEq-Header×Tip = DecEqI.DecEq-×
  DecEq-Point×Tip  : DecEq (Point × Tip)
  DecEq-Point×Tip  = DecEqI.DecEq-×
  DecEq-ListPoint  : DecEq (List Point)
  DecEq-ListPoint  = DecEqI.DecEq-List

------------------------------------------------------------------------
-- CSP operators over the small ChainSync alphabet.
------------------------------------------------------------------------

import CSP.Operators {E = CSEv} as CSOps
open CSOps CSEv-≟

------------------------------------------------------------------------
-- Step 4: the client (consumer) peer.
------------------------------------------------------------------------

-- unified ChainSync peer state (both peers walk the same FSM; agency differs).
data CSState : Set where
  stIdle      : CSState   -- Idle: client offers the api / server awaits a request
  stCanAwait  : CSState   -- CanAwait: server may roll or await; client awaiting reply
  stMustReply : CSState   -- MustReply: after AwaitReply, server must roll
  stIntersect : CSState   -- Intersect: awaiting / offering the intersect result
  stDone      : CSState   -- terminal (√)

instance
  -- decidable equality on the unified ChainSync state
  DecEq-CSState : DecEq CSState
  DecEq-CSState ._≟_ = go
    where
    go : (x y : CSState) → Dec (x ≡ y)
    go stIdle      stIdle      = yes refl
    go stCanAwait  stCanAwait  = yes refl
    go stMustReply stMustReply = yes refl
    go stIntersect stIntersect = yes refl
    go stDone      stDone      = yes refl
    go stIdle      stCanAwait  = no λ ()
    go stIdle      stMustReply = no λ ()
    go stIdle      stIntersect = no λ ()
    go stIdle      stDone      = no λ ()
    go stCanAwait  stIdle      = no λ ()
    go stCanAwait  stMustReply = no λ ()
    go stCanAwait  stIntersect = no λ ()
    go stCanAwait  stDone      = no λ ()
    go stMustReply stIdle      = no λ ()
    go stMustReply stCanAwait  = no λ ()
    go stMustReply stIntersect = no λ ()
    go stMustReply stDone      = no λ ()
    go stIntersect stIdle      = no λ ()
    go stIntersect stCanAwait  = no λ ()
    go stIntersect stMustReply = no λ ()
    go stIntersect stDone      = no λ ()
    go stDone      stIdle      = no λ ()
    go stDone      stCanAwait  = no λ ()
    go stDone      stMustReply = no λ ()
    go stDone      stIntersect = no λ ()

-- one client step (the body of the `iter` loop)
clientStep : Link → Dir → CSState → PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)
clientStep l d stIdle = pchoice v
  where
  v : (at : AnyTypes CSEv)
    → ContinueType at (Maybe (PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)))
  v (_ , apiCSev l′ d′ sendCSRequestNext) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ⟶
           Ret (inj₁ stCanAwait))
  ... | _        | _        = nothing
  v (_ , apiCSev l′ d′ sendCSFindIntersect) points with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect points)) ⟶
           Ret (inj₁ stIntersect))
  ... | _        | _        = nothing
  v (_ , apiCSev l′ d′ sendCSDone) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ⟶
           Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , apiCSev _ _ _) _ = nothing
  v (_ , sendCS _ _)    _ = nothing
  v (_ , receiveCS _ _) _ = nothing
  v (_ , doneCS _ _)    _ = nothing
clientStep l d stCanAwait = pchoice v
  where
  v : (at : AnyTypes CSEv)
    → ContinueType at (Maybe (PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)))
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward h t)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiCSev l d recvCSRollforward ! (h , t) ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward pt tp)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiCSev l d recvCSRollback ! (pt , tp) ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync MsgCSAwaitReply) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Ret (inj₁ stMustReply))
  ... | _        | _        = nothing
  v (_ , receiveCS _ _) _ = nothing
  v (_ , sendCS _ _)    _ = nothing
  v (_ , apiCSev _ _ _) _ = nothing
  v (_ , doneCS _ _)    _ = nothing
clientStep l d stMustReply = pchoice v
  where
  v : (at : AnyTypes CSEv)
    → ContinueType at (Maybe (PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)))
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward h t)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiCSev l d recvCSRollforward ! (h , t) ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward pt tp)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiCSev l d recvCSRollback ! (pt , tp) ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveCS _ _) _ = nothing
  v (_ , sendCS _ _)    _ = nothing
  v (_ , apiCSev _ _ _) _ = nothing
  v (_ , doneCS _ _)    _ = nothing
clientStep l d stIntersect = pchoice v
  where
  v : (at : AnyTypes CSEv)
    → ContinueType at (Maybe (PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)))
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound pt tp)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiCSev l d recvCSIntersectFound ! (pt , tp) ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound tp)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiCSev l d recvCSIntersectNotFound ! tp ⟶ Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , receiveCS _ _) _ = nothing
  v (_ , sendCS _ _)    _ = nothing
  v (_ , apiCSev _ _ _) _ = nothing
  v (_ , doneCS _ _)    _ = nothing
-- Done: successful termination (√)
clientStep _ _ stDone = Ret (inj₂ _)

-- the client peer: loop the step from the idle state
CSclientStClient : Link → Dir → PTree CSEv (ExtI CSEv) Rr
CSclientStClient l d = iter (clientStep l d) stIdle

------------------------------------------------------------------------
-- Step 5: the server (producer) peer — application-driven.
------------------------------------------------------------------------

-- one server step (the body of the `iter` loop)
serverStep : Link → Dir → CSState → PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)
serverStep l d stIdle = pchoice v
  where
  v : (at : AnyTypes CSEv)
    → ContinueType at (Maybe (PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)))
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync MsgCSRequestNext) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (apiCSev l d reqCSRequestNext ⟶₀ Ret (inj₁ stCanAwait))
  ... | _        | _        = nothing
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect points)) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (Output ⦃ DecEq-ListPoint ⦄ (apiCSev l d reqCSFindIntersect) points (Ret (inj₁ stIntersect)))
  ... | _        | _        = nothing
  v (_ , receiveCS l′ d′) (_ , _ , _ , chainSync MsgCSDone) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (doneCS l d ⟶₀ Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , receiveCS _ _) _ = nothing
  v (_ , sendCS _ _)    _ = nothing
  v (_ , apiCSev _ _ _) _ = nothing
  v (_ , doneCS _ _)    _ = nothing
serverStep l d stCanAwait = pchoice v
  where
  v : (at : AnyTypes CSEv)
    → ContinueType at (Maybe (PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)))
  v (_ , apiCSev l′ d′ sendCSRollForward) (h , t) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiCSev l′ d′ sendCSRollBackward) (pt , tp) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiCSev l′ d′ sendCSAwaitReply) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ⟶
           Ret (inj₁ stMustReply))
  ... | _        | _        = nothing
  v (_ , apiCSev _ _ _) _ = nothing
  v (_ , sendCS _ _)    _ = nothing
  v (_ , receiveCS _ _) _ = nothing
  v (_ , doneCS _ _)    _ = nothing
serverStep l d stMustReply = pchoice v
  where
  v : (at : AnyTypes CSEv)
    → ContinueType at (Maybe (PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)))
  v (_ , apiCSev l′ d′ sendCSRollForward) (h , t) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiCSev l′ d′ sendCSRollBackward) (pt , tp) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiCSev _ _ _) _ = nothing
  v (_ , sendCS _ _)    _ = nothing
  v (_ , receiveCS _ _) _ = nothing
  v (_ , doneCS _ _)    _ = nothing
serverStep l d stIntersect = pchoice v
  where
  v : (at : AnyTypes CSEv)
    → ContinueType at (Maybe (PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)))
  v (_ , apiCSev l′ d′ sendCSIntersectFound) (pt , tp) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiCSev l′ d′ sendCSIntersectNotFound) tp with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendCS l d ! (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ⟶
           Ret (inj₁ stIdle))
  ... | _        | _        = nothing
  v (_ , apiCSev _ _ _) _ = nothing
  v (_ , sendCS _ _)    _ = nothing
  v (_ , receiveCS _ _) _ = nothing
  v (_ , doneCS _ _)    _ = nothing
-- Done: successful termination (√)
serverStep _ _ stDone = Ret (inj₂ _)

-- the server peer: loop the step from the idle state
CSserverStClient : Link → Dir → PTree CSEv (ExtI CSEv) Rr
CSserverStClient l d = iter (serverStep l d) stIdle

------------------------------------------------------------------------
-- Step 6: network-fragment injection into `Net` (documentation stub).
------------------------------------------------------------------------

-- intended Net images of the ChainSync wire events (api/done: none)
ιCSNet : ∀ {A} → CSEv A → Maybe (Net Payload A)
ιCSNet (sendCS l d)    = just (input  l d N2N_ChainSync)
ιCSNet (receiveCS l d) = just (output l d N2N_ChainSync)
ιCSNet (apiCSev _ _ _) = nothing
ιCSNet (doneCS _ _)    = nothing

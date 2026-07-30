{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the KeepAlive mini-protocol peers
-- (realigned to the refactored `Net`).
--
-- The KeepAlive peers are written over their own small event type
-- `KAEv`, then (at the composition step, out of scope here) renamed into
-- the shared network alphabet `Net`.  This module ships the two peers
-- (`clientStClient` / `serverStClient`) plus the network-fragment
-- injection stub `ιKANet`.
--
-- It mirrors the reference state machines
--   KeepAliveClientPeer_StClient / KeepAliveClientPeer_StServer
--   KeepAliveServerPeer_StClient / KeepAliveServerPeer_StServer
-- from cardano_network/CSPM/mini_protocols.csp, and is kept *productive*
-- (no NON_TERMINATING): each peer is a non-recursive step function tied
-- with `iter`.
--
-- CSPm ↔ model differences:
--   1. Payload location: CSPm carries `t.m.l.msg` in the event label; here
--      `sendKA`/`receiveKA` negotiate it as the `?`/`!` value (`KAEv Payload`).
--   2. Pattern-input external choice → value-branching: CSPm's external
--      choice over `?`-patterns on one channel becomes value-branching
--      inside one `pchoice` on `receiveKA`, not a `□`.  On the receive
--      side the peers do not constrain the `Mode`/`Time`/`Length` payload
--      fields (they are behaviourally inert filler), whereas the CSPm
--      receive patterns pin the direction (`FromInitiator`/`FromResponder`).
--   3. Cookies bound from the api/wire: the server's request cookie and
--      the client's response cookie are bound from the negotiated payload;
--      the client's *request* cookie is bound from the api request event
--      `apiKAev c (sendKAMsg cookieReq)` via value-branching in `pchoice`
--      (no longer a meta-parameter — `stClient` carries no cookie).
--   4. API/Done/error are peer-local (`apiKAev`/`doneKA`): they have no
--      `Net` image and would be hidden before any rename.
--   5. `Time`/`Length` are abstract `Params` domains (CSPm enumerated them
--      only for FDR); the peers stamp the fillers `time₀`/`length₀`.
--   6. Productivity via `iter` (no NON_TERMINATING).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.KeepAlive (p : Params) where

open import Level renaming (zero to lzero)
import Data.Unit.Polymorphic as Poly
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees

open import CSP.Examples.Cardano_network.Base
import CSP.Examples.Cardano_network.Data as CardData
-- Open Data publicly so all names (including Payload/DecEq-Payload) are in local scope
-- AND re-exported, allowing `KeepAliveNetworkPar` to still retrieve them from `KeepAlive`.
open CardData p public
open import CSP.Examples.Cardano_network.Net  p

open Params p

instance
  -- `errCookie` negotiates a `Cookie × Cookie` carrier value, so the `!`
  -- output operator needs `DecEq (Cookie × Cookie)` in instance scope.
  -- The stdlib-classes `DecEq-×` is intentionally not an instance, so we
  -- expose it locally over `Cookie`.
  DecEq-Cookie² : DecEq (Cookie × Cookie)
  DecEq-Cookie² = DecEqI.DecEq-×

------------------------------------------------------------------------
-- Step 2: the per-protocol event type `KAEv`.
--
-- Network events negotiate `Payload`; the application-facing api/done
-- events are peer-local and `⊤`-carried.
------------------------------------------------------------------------

data KAEv : Set → Set where
  sendKA    : Link → Dir → KAEv Payload   -- peer→net (→ input);  emitted via !
  receiveKA : Link → Dir → KAEv Payload   -- net→peer (→ output); bound via ?
  apiKAev   : (l : Link) (d : Dir) (m : ApiKATag) → KAEv (ApiKACar m)  -- peer-local: SendKAMsg* / errCookie
  doneKA    : Link → Dir → KAEv ⊤          -- peer-local: Done

------------------------------------------------------------------------
-- Step 3: decidable equality on `AnyTypes KAEv`.
------------------------------------------------------------------------

KAEv-≟ : (x y : AnyTypes KAEv) → Dec (x ≡ y)
KAEv-≟ = go
  where
  go : (x y : AnyTypes KAEv) → Dec (x ≡ y)
  go (_ , sendKA l₁ d₁)     (_ , sendKA l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , receiveKA l₁ d₁)  (_ , receiveKA l₂ d₂)  with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiKAev l₁ d₁ m₁) (_ , apiKAev l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneKA l₁ d₁)     (_ , doneKA l₂ d₂)     with l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendKA _ _)    (_ , receiveKA _ _) = no λ ()
  go (_ , sendKA _ _)    (_ , apiKAev _ _ _) = no λ ()
  go (_ , sendKA _ _)    (_ , doneKA _ _)    = no λ ()
  go (_ , receiveKA _ _) (_ , sendKA _ _)    = no λ ()
  go (_ , receiveKA _ _) (_ , apiKAev _ _ _) = no λ ()
  go (_ , receiveKA _ _) (_ , doneKA _ _)    = no λ ()
  go (_ , apiKAev _ _ _) (_ , sendKA _ _)    = no λ ()
  go (_ , apiKAev _ _ _) (_ , receiveKA _ _) = no λ ()
  go (_ , apiKAev _ _ _) (_ , doneKA _ _)    = no λ ()
  go (_ , doneKA _ _)    (_ , sendKA _ _)    = no λ ()
  go (_ , doneKA _ _)    (_ , receiveKA _ _) = no λ ()
  go (_ , doneKA _ _)    (_ , apiKAev _ _ _) = no λ ()

------------------------------------------------------------------------
-- Step 4: peer return type and its DecEq.
------------------------------------------------------------------------

Rr : Set
Rr = Poly.⊤ {lzero}

instance
  DecEq-Rr : DecEq Rr
  DecEq-Rr = record { _≟_ = λ _ _ → yes refl }

------------------------------------------------------------------------
-- CSP operators over the small KeepAlive alphabet.
------------------------------------------------------------------------

import CSP.Operators {E = KAEv} as KAOps
open KAOps KAEv-≟

------------------------------------------------------------------------
-- Step 5: the client peer.
--
-- `stClient` mirrors KeepAliveClientPeer_StClient (offer the api: either a
-- request — binding `cookieReq` from `apiKAev c (sendKAMsg cookieReq)` via
-- value-branching in `pchoice` — or a done); `stServer cookieReq` mirrors
-- KeepAliveClientPeer_StServer (receive the response, bind `cookieRsp`,
-- guard the cookie match).
------------------------------------------------------------------------

-- unified KeepAlive peer state (both peers walk the same FSM; agency differs).
-- `stClient`: StClient (client offers the api / server awaits a request);
-- `stServer cookie`: StServer (client awaits the response to `cookie` /
-- server about to echo it); `stDone`: terminal (√).
data KAState : Set where
  stClient :          KAState
  stServer : Cookie → KAState
  stDone   :          KAState

instance
  -- decidable equality on the unified KeepAlive state
  DecEq-KAState : DecEq KAState
  DecEq-KAState ._≟_ = go
    where
    go : (x y : KAState) → Dec (x ≡ y)
    go stClient     stClient     = yes refl
    go (stServer a) (stServer b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go stDone       stDone       = yes refl
    go stClient     (stServer _) = no λ ()
    go stClient     stDone       = no λ ()
    go (stServer _) stClient     = no λ ()
    go (stServer _) stDone       = no λ ()
    go stDone       stClient     = no λ ()
    go stDone       (stServer _) = no λ ()

clientStep : Link → Dir → KAState → PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)
clientStep l d stClient = pchoice v
  where
  v : (at : AnyTypes KAEv)
    → ContinueType at (Maybe (PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)))
  v (_ , apiKAev l′ d′ sendKAMsg) cookieReq with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendKA l d ! (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive cookieReq)) ⟶
           Ret (inj₁ (stServer cookieReq)))
  ... | _        | _        = nothing
  v (_ , apiKAev l′ d′ sendKADone) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
        (sendKA l d ! (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ⟶
           Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , apiKAev _ _ errCookie) _ = nothing
  v (_ , apiKAev _ _ recvKACookie) _ = nothing   -- server-only api; client never offers it
  v (_ , sendKA _ _)    _ = nothing
  v (_ , receiveKA _ _) _ = nothing
  v (_ , doneKA _ _)    _ = nothing
clientStep l d (stServer cookieReq) = pchoice v
  where
  v : (at : AnyTypes KAEv)
    → ContinueType at (Maybe (PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)))
  v (_ , receiveKA l′ d′) (_ , _ , _ , keepAlive (MsgKeepAliveResponse cookieRsp))
    with l′ ≟ l | d′ ≟ d
  ... | no _      | _       = nothing
  ... | _         | no _    = nothing
  ... | yes refl  | yes refl with cookieReq ≟ cookieRsp
  ...   | yes _ = just (Ret (inj₁ stClient))
  ...   | no  _ = just (apiKAev l d errCookie ! (cookieReq , cookieRsp) ⟶ Ret (inj₂ _))
  v (_ , receiveKA _ _) _ = nothing
  v (_ , sendKA _ _)    _ = nothing
  v (_ , apiKAev _ _ _) _ = nothing
  v (_ , doneKA _ _)    _ = nothing
-- StDone: successful termination (√)
clientStep _ _ stDone = Ret (inj₂ _)

KAclientStClient : Link → Dir → PTree KAEv (ExtI KAEv) Rr
KAclientStClient l d = iter (clientStep l d) stClient

------------------------------------------------------------------------
-- Step 6: the server peer.
--
-- `stClient` mirrors KeepAliveServerPeer_StClient (receive a request —
-- binding `cookieReq` from the wire — or a done); `stServer cookieReq`
-- mirrors KeepAliveServerPeer_StServer (send the echoed response).
-- The `cookie` argument of `serverStClient` is retained for call-site
-- symmetry with the client; the server binds the real cookie from the
-- wire, so it is otherwise unused.
------------------------------------------------------------------------

serverStep : Link → Dir → KAState → PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)
serverStep l d stClient = pchoice v
  where
  v : (at : AnyTypes KAEv)
    → ContinueType at (Maybe (PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)))
  v (_ , receiveKA l′ d′) (_ , _ , _ , keepAlive (MsgKeepAlive cookieReq)) with l′ ≟ l | d′ ≟ d
  -- fire the server-side api `recvKACookie` reporting the received cookie, then loop
  ... | yes refl | yes refl = just (apiKAev l d recvKACookie ! cookieReq ⟶ Ret (inj₁ (stServer cookieReq)))
  ... | _        | _        = nothing
  v (_ , receiveKA l′ d′) (_ , _ , _ , keepAlive MsgKADone) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just (doneKA l d ⟶₀ Ret (inj₁ stDone))
  ... | _        | _        = nothing
  v (_ , receiveKA _ _) _ = nothing
  v (_ , sendKA _ _)    _ = nothing
  v (_ , apiKAev _ _ _) _ = nothing
  v (_ , doneKA _ _)    _ = nothing
serverStep l d (stServer cookieReq) =
  sendKA l d ! (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse cookieReq)) ⟶
    Ret (inj₁ stClient)
-- StDone: successful termination (√)
serverStep _ _ stDone = Ret (inj₂ _)

KAserverStClient : Link → Dir → PTree KAEv (ExtI KAEv) Rr
KAserverStClient l d = iter (serverStep l d) stClient

------------------------------------------------------------------------
-- Step 7: network-fragment injection into `Net` (documentation stub).
--
-- `CSP.Rename` needs a *total* `ι : KAEv A → Net Payload A`, which is
-- impossible while api/done have no `Net` image.  This `Maybe`-valued
-- helper records the intended images of the *network* events only;
-- api/done are `nothing` (peer-local, hidden before any real rename).
-- The total `ι` (over the residual alphabet after hiding) and the
-- `renameMap`/`Par` composition are built at the composition step.
------------------------------------------------------------------------

ιKANet : ∀ {A} → KAEv A → Maybe (Net Payload A)
ιKANet (sendKA l d)    = just (input  l d N2N_KeepAlive)
ιKANet (receiveKA l d) = just (output l d N2N_KeepAlive)
ιKANet (apiKAev _ _ _) = nothing
ιKANet (doneKA _ _)    = nothing

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
  sendKA    : Conn N2N_KeepAlive → KAEv Payload   -- peer→net (→ input);  emitted via !
  receiveKA : Conn N2N_KeepAlive → KAEv Payload   -- net→peer (→ output); bound via ?
  apiKAev   : (c : Conn N2N_KeepAlive) (m : ApiKATag) → KAEv (ApiKACar m)  -- peer-local: SendKAMsg* / errCookie
  doneKA    : Conn N2N_KeepAlive → KAEv ⊤          -- peer-local: Done

------------------------------------------------------------------------
-- Step 3: decidable equality on `AnyTypes KAEv`.
------------------------------------------------------------------------

KAEv-≟ : (x y : AnyTypes KAEv) → Dec (x ≡ y)
KAEv-≟ = go
  where
  go : (x y : AnyTypes KAEv) → Dec (x ≡ y)
  go (_ , sendKA c₁)     (_ , sendKA c₂)     with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , receiveKA c₁)  (_ , receiveKA c₂)  with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiKAev c₁ m₁) (_ , apiKAev c₂ m₂) with c₁ ≟ c₂ | m₁ ≟ m₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneKA c₁)     (_ , doneKA c₂)     with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendKA _)    (_ , receiveKA _) = no λ ()
  go (_ , sendKA _)    (_ , apiKAev _ _) = no λ ()
  go (_ , sendKA _)    (_ , doneKA _)    = no λ ()
  go (_ , receiveKA _) (_ , sendKA _)    = no λ ()
  go (_ , receiveKA _) (_ , apiKAev _ _) = no λ ()
  go (_ , receiveKA _) (_ , doneKA _)    = no λ ()
  go (_ , apiKAev _ _) (_ , sendKA _)    = no λ ()
  go (_ , apiKAev _ _) (_ , receiveKA _) = no λ ()
  go (_ , apiKAev _ _) (_ , doneKA _)    = no λ ()
  go (_ , doneKA _)    (_ , sendKA _)    = no λ ()
  go (_ , doneKA _)    (_ , receiveKA _) = no λ ()
  go (_ , doneKA _)    (_ , apiKAev _ _) = no λ ()

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

clientStep : Conn N2N_KeepAlive → KAState → PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)
clientStep c stClient = pchoice v
  where
  v : (at : AnyTypes KAEv)
    → ContinueType at (Maybe (PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)))
  v (_ , apiKAev c′ sendKAMsg) cookieReq with c′ ≟ c
  ... | yes refl = just
        (sendKA c ! (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive cookieReq)) ⟶
           Ret (inj₁ (stServer cookieReq)))
  ... | no _     = nothing
  v (_ , apiKAev c′ sendKADone) _ with c′ ≟ c
  ... | yes refl = just
        (sendKA c ! (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ⟶
           (doneKA c ⟶₀ Ret (inj₁ stDone)))
  ... | no _     = nothing
  v (_ , apiKAev _ errCookie) _ = nothing
  v (_ , sendKA _)    _ = nothing
  v (_ , receiveKA _) _ = nothing
  v (_ , doneKA _)    _ = nothing
clientStep c (stServer cookieReq) = pchoice v
  where
  v : (at : AnyTypes KAEv)
    → ContinueType at (Maybe (PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)))
  v (_ , receiveKA c′) (_ , _ , _ , keepAlive (MsgKeepAliveResponse cookieRsp))
    with c′ ≟ c
  ... | no _      = nothing
  ... | yes refl  with cookieReq ≟ cookieRsp
  ...   | yes _ = just (Ret (inj₁ stClient))
  ...   | no  _ = just (apiKAev c errCookie ! (cookieReq , cookieRsp) ⟶ Ret (inj₂ _))
  v (_ , receiveKA _) _ = nothing
  v (_ , sendKA _)    _ = nothing
  v (_ , apiKAev _ _) _ = nothing
  v (_ , doneKA _)    _ = nothing
-- StDone: successful termination (√)
clientStep _ stDone = Ret (inj₂ _)

KAclientStClient : Conn N2N_KeepAlive → PTree KAEv (ExtI KAEv) Rr
KAclientStClient c = iter (clientStep c) stClient

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

serverStep : Conn N2N_KeepAlive → KAState → PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)
serverStep c stClient = pchoice v
  where
  v : (at : AnyTypes KAEv)
    → ContinueType at (Maybe (PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)))
  v (_ , receiveKA c′) (_ , _ , _ , keepAlive (MsgKeepAlive cookieReq)) with c′ ≟ c
  ... | yes refl = just (Ret (inj₁ (stServer cookieReq)))
  ... | no _     = nothing
  v (_ , receiveKA c′) (_ , _ , _ , keepAlive MsgKADone) with c′ ≟ c
  ... | yes refl = just (doneKA c ⟶₀ Ret (inj₁ stDone))
  ... | no _     = nothing
  v (_ , receiveKA _) _ = nothing
  v (_ , sendKA _)    _ = nothing
  v (_ , apiKAev _ _) _ = nothing
  v (_ , doneKA _)    _ = nothing
serverStep c (stServer cookieReq) =
  sendKA c ! (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse cookieReq)) ⟶
    Ret (inj₁ stClient)
-- StDone: successful termination (√)
serverStep _ stDone = Ret (inj₂ _)

KAserverStClient : Conn N2N_KeepAlive → PTree KAEv (ExtI KAEv) Rr
KAserverStClient c = iter (serverStep c) stClient

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
ιKANet (sendKA c)    = just (input  N2N_KeepAlive c)
ιKANet (receiveKA c) = just (output N2N_KeepAlive c)
ιKANet (apiKAev _ _) = nothing
ιKANet (doneKA _)    = nothing

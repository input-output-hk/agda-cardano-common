{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the KeepAlive mini-protocol peer
-- (architecture-validating module).
--
-- This module demonstrates the per-protocol pattern of the design: the
-- KeepAlive peers are written over their *own* small event type `KAEv`
-- (only this protocol's channels, all ⊤-carried) using the CSP
-- operators, then renamed **into** the shared network alphabet `Net`
-- via the generalized `renameMap` with the injection `ιKA : KAEv → Net`.
--
-- Per the design's encoding decision §1, the abstract `Cookie` domain is
-- kept opaque, so the peers are **meta-parametrised** over cookie values
-- rather than enumerating them: a peer is an Agda function
-- `peer (c : Conn …) (cookie : Cookie) → ITree …`, defined for any
-- `cookie`, with the value carried in the message label
-- (`sendKA c … (keepAlive (MsgKeepAlive cookie))`). The cookie-match
-- guard `cookieReq == cookieRsp` of the reference `.csp` becomes a
-- decidable test `cookieReq ≟ cookieRsp` using the `DecEq Cookie`
-- instance threaded through `Params`.
--
-- The peers mirror the reference state machines
--   KeepAliveClientPeer_StClient / KeepAliveClientPeer_StServer
--   KeepAliveServerPeer_StClient / KeepAliveServerPeer_StServer
-- from Study/Networks/Mini-protocols/mini_protocols.csp, and are kept
-- *productive* (no NON_TERMINATING): every recursive reference sits
-- syntactically under a prefix (`⟶`).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.KeepAlive (p : Params) where

open import Level using (Lift) renaming (zero to lzero)
import Data.Unit.Polymorphic as Poly
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero)
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

-- abstract domains (Cookie + DecEq) and numConns in scope
open Params p
open PTree

------------------------------------------------------------------------
-- Step 1: the per-protocol event type `KAEv` (all ⊤-carried).
--
-- The protocol id is fixed to `N2N_KeepAlive`, so the connection is
-- `Conn N2N_KeepAlive`. The two `ℕ`s are Time and Length (kept `0` by
-- the peers, mirroring `timeat.0` / length `0` of the `.csp`).
------------------------------------------------------------------------

data KAEv : Set → Set where
  sendKA    : Conn N2N_KeepAlive → ℕ → Mode → ℕ → Messages → KAEv ⊤
  receiveKA : Conn N2N_KeepAlive → ℕ → Mode → ℕ → Messages → KAEv ⊤
  apiKAev   : Conn N2N_KeepAlive → ApiKA → KAEv ⊤
  doneKA    : Conn N2N_KeepAlive → KAEv ⊤

------------------------------------------------------------------------
-- Step 2: decidable equality on `AnyTypes KAEv`.
--
-- Every event is `KAEv ⊤`. The `Conn N2N_KeepAlive` arguments compare
-- by `Fin`'s `DecEq`; the `Messages`/`ApiKA`/`Mode` payloads via the
-- in-scope instances; cross-constructor cases are `no λ ()`.
------------------------------------------------------------------------

KAEv-≟ : (x y : AnyTypes KAEv) → Dec (x ≡ y)
KAEv-≟ = go
  where
  go : (x y : AnyTypes KAEv) → Dec (x ≡ y)
  go (_ , sendKA c₁ t₁ m₁ l₁ d₁) (_ , sendKA c₂ t₂ m₂ l₂ d₂)
    with c₁ ≟ c₂ | t₁ ≟ t₂ | m₁ ≟ m₂ | l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ | _ | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p | _ | _ | _ = no λ where refl → ¬p refl
  ... | _ | _ | no ¬p | _ | _ = no λ where refl → ¬p refl
  ... | _ | _ | _ | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | _ | _ | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , receiveKA c₁ t₁ m₁ l₁ d₁) (_ , receiveKA c₂ t₂ m₂ l₂ d₂)
    with c₁ ≟ c₂ | t₁ ≟ t₂ | m₁ ≟ m₂ | l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ | _ | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p | _ | _ | _ = no λ where refl → ¬p refl
  ... | _ | _ | no ¬p | _ | _ = no λ where refl → ¬p refl
  ... | _ | _ | _ | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | _ | _ | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , apiKAev c₁ a₁) (_ , apiKAev c₂ a₂) with c₁ ≟ c₂ | a₁ ≟ a₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , doneKA c₁) (_ , doneKA c₂) with c₁ ≟ c₂
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  go (_ , sendKA _ _ _ _ _)    (_ , receiveKA _ _ _ _ _) = no λ ()
  go (_ , sendKA _ _ _ _ _)    (_ , apiKAev _ _)         = no λ ()
  go (_ , sendKA _ _ _ _ _)    (_ , doneKA _)            = no λ ()
  go (_ , receiveKA _ _ _ _ _) (_ , sendKA _ _ _ _ _)    = no λ ()
  go (_ , receiveKA _ _ _ _ _) (_ , apiKAev _ _)         = no λ ()
  go (_ , receiveKA _ _ _ _ _) (_ , doneKA _)            = no λ ()
  go (_ , apiKAev _ _)         (_ , sendKA _ _ _ _ _)    = no λ ()
  go (_ , apiKAev _ _)         (_ , receiveKA _ _ _ _ _) = no λ ()
  go (_ , apiKAev _ _)         (_ , doneKA _)            = no λ ()
  go (_ , doneKA _)            (_ , sendKA _ _ _ _ _)    = no λ ()
  go (_ , doneKA _)            (_ , receiveKA _ _ _ _ _) = no λ ()
  go (_ , doneKA _)            (_ , apiKAev _ _)         = no λ ()

------------------------------------------------------------------------
-- Step 3: return type for the peers and its DecEq (needed by `□`).
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
-- Step 4: the peers (over `ITree KAEv (ExtI KAEv) Rr`).
--
-- Meta-parametrised over the abstract cookie values (design §1): the
-- request cookie rides in the loop *state* as a meta-parameter. Time and
-- Length are fixed to `0` (zero); the direction is the protocol `Mode`.
--
-- Productivity. Direct mutual corecursion through the CSP combinators
-- (`⟶₀`/`□`) is NOT seen as guarded by Agda's termination checker —
-- `Prefix₀`/`_□_` are *functions*, not constructors, so the checker
-- cannot find the guarding `vis` they ultimately produce. The framework
-- supplies a productive fixed-point combinator for exactly this:
-- `iter : (A → ITree … (A ⊎ R)) → A → ITree … R`, whose own `force`
-- inserts a `Tau` between iterations (so the loop is guarded by `iter`,
-- not by us). We therefore present each peer as a single non-recursive
-- *step function* over an explicit protocol-state type, and tie the knot
-- with `iter`. No NON_TERMINATING pragma is used.
--
-- Faithfulness. The state machines mirror the reference
-- `KeepAliveClientPeer_StClient/StServer` and `KeepAliveServerPeer_*`
-- one-for-one (same events, same order, same external choices, same
-- cookie-match guard). The only encoding shift forced by the abstract
-- `Cookie` domain is that the reference `?cookieReq`/`?cookieRsp` value
-- inputs become the loop's `Cookie` meta-parameter (design §1); the
-- response is taken to echo the request (the protocol-conformant case),
-- which is the value carried in the `receiveKA …` label.
------------------------------------------------------------------------

-- Explicit protocol-state types (carry the in-flight cookie). `DecEq`
-- is needed because the loop step ends in `Ret (inj_ …) : A ⊎ Rr` and
-- the `□` of the two StClient branches requires `DecEq (A ⊎ Rr)`.

data CState : Set where
  cClient : Cookie → CState   -- StClient, about to request with this cookie
  cServer : Cookie → CState   -- StServer, awaiting the response to this cookie

data SState : Set where
  sClient : Cookie → SState   -- StClient (server side), awaiting a request
  sServer : Cookie → SState   -- StServer (server side), about to respond

instance
  DecEq-CState : DecEq CState
  DecEq-CState ._≟_ = go
    where
    go : (x y : CState) → Dec (x ≡ y)
    go (cClient a) (cClient b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (cServer a) (cServer b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (cClient _) (cServer _) = no λ ()
    go (cServer _) (cClient _) = no λ ()

  DecEq-SState : DecEq SState
  DecEq-SState ._≟_ = go
    where
    go : (x y : SState) → Dec (x ≡ y)
    go (sClient a) (sClient b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sServer a) (sServer b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sClient _) (sServer _) = no λ ()
    go (sServer _) (sClient _) = no λ ()

-- Client peer ---------------------------------------------------------

clientStep : Conn N2N_KeepAlive → CState → PTree KAEv (ExtI KAEv) (CState ⊎ Rr)
-- StClient: either send a keepalive request carrying `cookieReq` and
-- move to StServer, or send Done and terminate.
clientStep c (cClient cookieReq) =
  (apiKAev c (sendKAMsg cookieReq)
     ⟶₀ (sendKA c zero FromInitiator zero (keepAlive (MsgKeepAlive cookieReq))
     ⟶₀ Ret (inj₁ (cServer cookieReq))))
  □
  (apiKAev c sendKADone
     ⟶₀ (sendKA c zero FromInitiator zero (keepAlive MsgKADone)
     ⟶₀ (doneKA c
     ⟶₀ Ret (inj₂ _))))
-- StServer: receive the response (echoing `cookieReq`), then a guarded
-- choice on the cookie match. Match ⇒ loop back to StClient; mismatch ⇒
-- signal the error and terminate. Decided by `cookieReq ≟ cookieRsp`
-- (here the response echoes the request, so the match branch is taken).
clientStep c (cServer cookieReq) =
  receiveKA c zero FromResponder zero (keepAlive (MsgKeepAliveResponse cookieReq))
    ⟶₀ step
  where
  cookieRsp : Cookie
  cookieRsp = cookieReq
  step : PTree KAEv (ExtI KAEv) (CState ⊎ Rr)
  step with cookieReq ≟ cookieRsp
  ... | yes _ = Ret (inj₁ (cClient cookieReq))
  ... | no  _ = apiKAev c (errCookie cookieReq cookieRsp) ⟶₀ Ret (inj₂ _)

clientStClient : Conn N2N_KeepAlive → Cookie → PTree KAEv (ExtI KAEv) Rr
clientStClient c cookie = iter (clientStep c) (cClient cookie)

-- Server peer ---------------------------------------------------------

serverStep : Conn N2N_KeepAlive → SState → PTree KAEv (ExtI KAEv) (SState ⊎ Rr)
-- StClient (server side): receive either a keepalive request (carrying
-- `cookieReq`) and move to StServer, or a Done and terminate.
serverStep c (sClient cookieReq) =
  (receiveKA c zero FromInitiator zero (keepAlive (MsgKeepAlive cookieReq))
     ⟶₀ Ret (inj₁ (sServer cookieReq)))
  □
  (receiveKA c zero FromInitiator zero (keepAlive MsgKADone)
     ⟶₀ (doneKA c
     ⟶₀ Ret (inj₂ _)))
-- StServer (server side): send the response echoing `cookieReq`, then
-- loop back to StClient.
serverStep c (sServer cookieReq) =
  sendKA c zero FromResponder zero (keepAlive (MsgKeepAliveResponse cookieReq))
    ⟶₀ Ret (inj₁ (sClient cookieReq))

serverStClient : Conn N2N_KeepAlive → Cookie → PTree KAEv (ExtI KAEv) Rr
serverStClient c cookie = iter (serverStep c) (sClient cookie)

------------------------------------------------------------------------
-- Step 5: the injection `KAEv → Net` (textbook CSP renaming).
--
--   sendKA c t m l d ↦ input  N2N_KeepAlive c t m l d
--   receiveKA c …    ↦ output N2N_KeepAlive c …
--   apiKAev c a      ↦ apiKA  c a
--   doneKA c         ↦ done   N2N_KeepAlive c
------------------------------------------------------------------------

ιKA : ∀ {A} → KAEv A → Net A
ιKA (sendKA c t m l d)    = input  N2N_KeepAlive c t m l d
ιKA (receiveKA c t m l d) = output N2N_KeepAlive c t m l d
ιKA (apiKAev c a)         = apiKA c a
ιKA (doneKA c)            = done N2N_KeepAlive c

ιKA⁻¹ : ∀ {A} → Net A → Maybe (KAEv A)
ιKA⁻¹ (input  N2N_KeepAlive c t m l d) = just (sendKA c t m l d)
ιKA⁻¹ (output N2N_KeepAlive c t m l d) = just (receiveKA c t m l d)
ιKA⁻¹ (apiKA c a)                      = just (apiKAev c a)
ιKA⁻¹ (done N2N_KeepAlive c)           = just (doneKA c)
ιKA⁻¹ _                                = nothing

ιKA-linv : ∀ {A} (e : KAEv A) → ιKA⁻¹ (ιKA e) ≡ just e
ιKA-linv (sendKA c t m l d)    = refl
ιKA-linv (receiveKA c t m l d) = refl
ιKA-linv (apiKAev c a)         = refl
ιKA-linv (doneKA c)            = refl

------------------------------------------------------------------------
-- Step 6: rename the peers onto the shared `Net` alphabet and compose
-- them by interleaving (parallel with empty sync set over `Net`).
------------------------------------------------------------------------

import CSP.Rename {E₁ = KAEv} {E₂ = Net} ιKA ιKA⁻¹ ιKA-linv as RenKA
import CSP.Operators {E = Net} Net-≟ as NetPar

-- empty synchronisation set over `Net` (interleaving): no event synchs.
∅Net : AnyTypes Net → Set
∅Net _ = ⊥

∅Net-dec : (at : AnyTypes Net) → Dec (∅Net at)
∅Net-dec _ = no λ ()

-- The interleave's natural return type is `Rr × Rr` (the framework's
-- `_∥⇘_⇙_` returns `R × S`); since `Rr = Poly.⊤`, this is `Poly.⊤`-like
-- and `DecEq`-decidable. Downstream `Top` composes this interleave with
-- `Network` over the same empty/`netSync` set.
KeepAlivePeer : Conn N2N_KeepAlive → Cookie → PTree Net (ExtI Net) (Rr × Rr)
KeepAlivePeer c cookie =
  NetPar.Par ∅Net ∅Net-dec _,_
    (RenKA.renameMap (clientStClient c cookie))
    (RenKA.renameMap (serverStClient c cookie))

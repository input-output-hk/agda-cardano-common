{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeiosNotify with a PIPELINED client and a READ-AHEAD server (ouroboros-consensus PR 2344),
-- over the same alphabet `LNPEv`, payloads, messages and api tags as `LeiosNotifyP` (no new
-- tag, no new message).  Properties are in `LeiosNotifyPipelinedProps.agda`.
--
-- UPSTREAM (PR 2344).  The consensus-side client is PIPELINED: it may send MsgQuit while
-- requests are still outstanding, and from then on it IGNORES (does not deliver) the replies
-- / MsgCanceled still owed for them, awaiting MsgDone.  The network-side server READS AHEAD:
-- when MsgQuit arrives while it still owes replies, it answers every outstanding request
-- with MsgCanceled and then sends MsgDone.  In protocol order (each client message followed
-- by its answer) this is still the blueprint table of `LeiosNotifyP` — the pipelining only
-- moves the client's SEND of MsgQuit earlier than its predicted StIdle.
--
-- THE ABSTRACTION: DEPTH 1.  At most one request is outstanding (upstream's depth bound is
-- abstracted to 1).  Both peers loop over the table state `LNPState` and REUSE the rounds of
-- `LeiosNotifyP` verbatim; pipelining is exactly ONE extra transition per peer, in StBusy:
--   * client (`pcStep`), its loop state = (table state it sends from, replies owed, drain):
--       stIdle  (StIdle, 0 owed)   `clientStepP l d stIdle`: RequestNext → stBusy, or the
--                                  quit command `lnpSendDone` → MsgQuit → stQuit;
--       stBusy  (StIdle predicted, 1 owed)   `clientStepP l d stBusy`'s menu — the owed reply
--                                  (the four notifications delivered to the api, MsgCanceled
--                                  accepted silently) → stIdle — PLUS the PIPELINED QUIT:
--                                  `lnpSendDone` → MsgQuit → `drainP` (1 owed, draining):
--                                  the owed reply or MsgCanceled is received and DISCARDED
--                                  (exactly the StBusy menu, no delivery) → stQuit;
--       stQuit  (StQuit, 0 owed)   `clientStepP l d stQuit`: MsgDone → End (√).
--     No second RequestNext while one is owed (the stBusy menu has no such api offer).
--   * server (`psStep`), its loop state = (table state, holds a request?, quit received?):
--       stIdle  `serverStepP l d stIdle`: RequestNext → stBusy, MsgQuit → stQuit;
--       stBusy  (holds one request)   `serverStepP l d stBusy`'s api-driven reply — the four
--               notifications or `lnpSendCanceled` → stIdle — PLUS the READ-AHEAD: MsgQuit
--               is read while the request is held, answered by MsgCanceled (`readAhead`), → stQuit;
--       stQuit  `serverStepP l d stQuit`: `doneLNP`, MsgDone, End (√).
--   TABLE SEMANTICS FOR CANCEL: as in `LeiosNotifyP`, the server application may cancel a
--   held request at ANY time (`lnpSendCanceled`), not only after a quit; the read-ahead
--   cancel is the additional, application-free one.
--
-- THE CHANNEL: TWO ONE-WAY FIFOs.  Pipelined messages CROSS (MsgQuit travels towards the
-- server while the reply travels towards the client), so the pair cannot rendezvous
-- directly as `LeiosNotifyQuit.sys` does.  `fifo l i o` is a capacity-2 FIFO taking the
-- sender's `sendLNP l i` and delivering it as the receiver's `receiveLNP l o`:
--     psys l = (client(l , lo) ⦀ server(l , hi)) [| wire |] (fifo l lo hi ⦀ fifo l hi lo)
-- (no renaming is needed: the buffers translate the channel names).  Capacity 2 is the
-- most ever in flight per direction at depth 1 (client→server: RequestNext then the
-- pipelined MsgQuit; server→client: the reply then MsgDone), so a buffer never refuses a
-- sender (`LeiosNotifyPipelinedProps.psys-noBlock`): the FIFOs behave as unbounded ones.
-- A FIFO CLOSES (√) after delivering its direction's last message (MsgQuit resp. MsgDone),
-- so a completed shutdown is the system's √.
--
-- MODELLING GAP.  The real per-instance medium (`Network.Copy`, see the header of
-- `LeiosNotifyQuitNet.agda`) is ONE one-place cell SHARED by both directions of an instance.
-- It cannot carry this traffic: with a request and the pipelined MsgQuit in flight, or a
-- reply crossing MsgQuit, a one-place shared cell blocks a sender (and, being shared,
-- serialises the two directions).  Pipelining needs per-direction buffering, which the
-- model's medium does not provide; `psys` is therefore a pair-level model over idealised
-- channels, not over `NetworkLink`.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosNotifyPipelined (p : Params) where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (_≟_)

open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p
open import Cardano_network.Parametric.Leios.LeiosNotifyQuit p using (Tree; wireES)
open Params p using (time₀; length₀)

open import CSP.Operators LNPEv-≟ using (Ret; Output; pchoice; iter; viewV; Par⊤; _⦀_)

------------------------------------------------------------------------
-- §1  Helpers
------------------------------------------------------------------------

-- a LeiosNotify round (one loop body over the table state)
Rd : Set₁
Rd = PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)

-- left-biased union of two offers: the first menu's offer, else the second's
orM : ∀ {A : Set₁} → Maybe A → Maybe A → Maybe A
orM (just t) _ = just t
orM nothing  m = m

------------------------------------------------------------------------
-- §2  The pipelined client
------------------------------------------------------------------------

-- the DRAIN menu (after a pipelined MsgQuit, one reply owed): exactly what the StBusy menu
-- of `clientStepP` accepts (the four replies and MsgCanceled), consumed WITHOUT delivery,
-- then StQuit (await MsgDone)
drainP : Link → Dir → Rd
drainP l d = pchoice λ at a →
  Maybe.map (λ _ → Ret (inj₁ stQuit)) (viewV (PTree.force (clientStepP l d stBusy)) at a)

-- the PIPELINED QUIT (one request outstanding): the application's quit command
-- `lnpSendDone` sends MsgQuit at once and enters the drain menu
pipeQuit : Link → Dir → (at : AnyTypes LNPEv) → ContinueType at (Maybe Rd)
pipeQuit l d (_ , apiLPev l′ d′ m) _ with l′ ≟ l | d′ ≟ d | m ≟ lnpSendDone
... | yes refl | yes refl | yes refl =
      just (sendLNP l d ! (time₀ , FromInitiator , length₀ , leiosNotifyP MsgLNPQuit) ⟶ drainP l d)
... | _        | _        | _        = nothing
pipeQuit _ _ (_ , sendLNP _ _)    _ = nothing
pipeQuit _ _ (_ , receiveLNP _ _) _ = nothing
pipeQuit _ _ (_ , doneLNP _ _)    _ = nothing

-- one round of the pipelined client: `clientStepP`'s own rounds, plus the pipelined quit
-- in StBusy (its loop state stBusy = "StIdle predicted, one reply owed")
pcStep : Link → Dir → LNPState → Rd
pcStep l d stIdle = clientStepP l d stIdle
pcStep l d stBusy = pchoice λ at a →
  orM (viewV (PTree.force (clientStepP l d stBusy)) at a) (pipeQuit l d at a)
pcStep l d stQuit = clientStepP l d stQuit

-- THE PIPELINED CLIENT (depth 1): loop the round from StIdle
LNPpipeClient : Link → Dir → Tree
LNPpipeClient l d = iter (pcStep l d) stIdle

------------------------------------------------------------------------
-- §3  The read-ahead server
------------------------------------------------------------------------

-- the READ-AHEAD (holding one request): MsgQuit is read, the held request is answered by
-- MsgCanceled (no application involved), then StQuit (`doneLNP`, MsgDone)
readAhead : Link → Dir → (at : AnyTypes LNPEv) → ContinueType at (Maybe Rd)
readAhead l d (_ , receiveLNP l′ d′) (_ , _ , _ , msg) with l′ ≟ l | d′ ≟ d | msg ≟ leiosNotifyP MsgLNPQuit
... | yes refl | yes refl | yes refl =
      just (sendLNP l d ! (time₀ , FromResponder , length₀ , leiosNotifyP MsgLNPCanceled) ⟶ Ret (inj₁ stQuit))
... | _        | _        | _        = nothing
readAhead _ _ (_ , sendLNP _ _)   _ = nothing
readAhead _ _ (_ , apiLPev _ _ _) _ = nothing
readAhead _ _ (_ , doneLNP _ _)   _ = nothing

-- one round of the read-ahead server: `serverStepP`'s own rounds, plus the read-ahead in
-- StBusy (the api-driven replies and `lnpSendCanceled` stay available: table semantics)
psStep : Link → Dir → LNPState → Rd
psStep l d stIdle = serverStepP l d stIdle
psStep l d stBusy = pchoice λ at a →
  orM (viewV (PTree.force (serverStepP l d stBusy)) at a) (readAhead l d at a)
psStep l d stQuit = serverStepP l d stQuit

-- THE READ-AHEAD SERVER: loop the round from StIdle
LNPreadAheadServer : Link → Dir → Tree
LNPreadAheadServer l d = iter (psStep l d) stIdle

------------------------------------------------------------------------
-- §4  The one-way FIFOs
------------------------------------------------------------------------

-- a FIFO's contents (capacity 2, head first)
data BSt : Set where
  β0 : BSt
  β1 : Payload → BSt
  β2 : Payload → Payload → BSt

-- a FIFO round
Bd : Set₁
Bd = PTree LNPEv (ExtI LNPEv) (BSt ⊎ Rr)

-- the last message of a direction: MsgQuit (client→server) or MsgDone (server→client)
isLast : Payload → Bool
isLast (_ , _ , _ , leiosNotifyP MsgLNPQuit) = true
isLast (_ , _ , _ , leiosNotifyP MsgLNPDone) = true
isLast _                                     = false

-- after a delivery: closed (√) if it was the last message, else empty again
afterB : Bool → BSt ⊎ Rr
afterB true  = inj₂ tt
afterB false = inj₁ β0

-- an input is accepted while there is room
inB : BSt → Payload → Maybe Bd
inB β0       x = just (Ret (inj₁ (β1 x)))
inB (β1 y)   x = just (Ret (inj₁ (β2 y x)))
inB (β2 _ _) _ = nothing

-- an output delivers exactly the head
outB : BSt → Payload → Maybe Bd
outB β0       _ = nothing
outB (β1 x)   y with y ≟ x
... | yes _ = just (Ret (afterB (isLast x)))
... | no  _ = nothing
outB (β2 x z) y with y ≟ x
... | yes _ = just (Ret (inj₁ (β1 z)))
... | no  _ = nothing

-- the FIFO's menu: input on `sendLNP l i`, output on `receiveLNP l o`
fifoV : Link → Dir → Dir → BSt → (at : AnyTypes LNPEv) → ContinueType at (Maybe Bd)
fifoV l i o b (_ , sendLNP l′ d′) x with l′ ≟ l | d′ ≟ i
... | yes refl | yes refl = inB b x
... | _        | _        = nothing
fifoV l i o b (_ , receiveLNP l′ d′) y with l′ ≟ l | d′ ≟ o
... | yes refl | yes refl = outB b y
... | _        | _        = nothing
fifoV _ _ _ _ (_ , apiLPev _ _ _) _ = nothing
fifoV _ _ _ _ (_ , doneLNP _ _)   _ = nothing

-- one FIFO round
fifoStep : Link → Dir → Dir → BSt → Bd
fifoStep l i o b = pchoice (fifoV l i o b)

-- THE ONE-WAY FIFO from `(l , i)`'s sends to `(l , o)`'s receives, initially empty
fifo : Link → Dir → Dir → Tree
fifo l i o = iter (fifoStep l i o) β0

------------------------------------------------------------------------
-- §5  The system
------------------------------------------------------------------------

-- the two peers: the pipelined client at `(l , lo)`, the read-ahead server at `(l , hi)`
peers : Link → Tree
peers l = LNPpipeClient l lo ⦀ LNPreadAheadServer l hi

-- the two one-way FIFOs: client→server and server→client
chans : Link → Tree
chans l = fifo l lo hi ⦀ fifo l hi lo

-- THE PIPELINED SYSTEM: the peers synchronised with the FIFOs on the wire; api / done open
psys : Link → Tree
psys l = Par⊤ (wireES l) (peers l) (chans l)

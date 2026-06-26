{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the multiplexer `Network` process.
--
-- A faithful PTree rendering of the CSPm `Network` from
--   Study/Networks/Mini-protocols/mini_protocols.csp  (lines 66–84):
--
--   Input(id)   = input.id?t.m.l.d -> sndmsg.id!t.m.l.d -> rcvack.id.t -> Input(id)
--   Output(id)  = rcvmsg.id?t.m.l.d -> output.id!t.m.l.d -> sndack.id!t -> Output(id)
--   Transmitter = [] id:IDs @ (sndmsg.id?t.m.l.d -> tx!id.t.m.l.d -> Transmitter)
--   Receiver    = [] id:IDs @ (tx?id.t.m.l.d -> rcvmsg.id!t.m.l.d -> Receiver)
--   SndAck      = [] id:IDs @ (sndack.id?t -> ack!id.t -> SndAck)
--   RcvAck      = [] id:IDs @ (ack?id.t -> rcvack.id.t -> RcvAck)
--   TxSide  = (Inputs  [|{|sndmsg,rcvack|}|] (Transmitter ||| RcvAck)) \ {|sndmsg,rcvack|}
--   RxSide  = (Outputs [|{|rcvmsg,sndack|}|] (Receiver    ||| SndAck)) \ {|rcvmsg,sndack|}
--   Network = (TxSide  [|{| tx, ack |}|]      RxSide) \ {| tx, ack |}
--
-- Adaptation to the refined `Net` type (see `Net.agda`):
--   * CSPm `Connection` becomes the explicit `Conn id` argument of each channel.
--   * CSPm `Time.Mode.Length.Messages` becomes the opaque payload `Data`; the
--     Network only *forwards* it, so this module is generic in `(Data : Set)`
--     with `⦃ DecEq Data ⦄` (the latter feeds `Net-≟` → `CSP.Operators`).
--   * The CSPm ack channels correlate a message with its acknowledgement by
--     `Time`; the refined `Net` ack channels carry `Conn id` instead, so here
--     the **connection `c`** is the correlation token threaded through
--     `input id c d → sndmsg id c d → rcvack id c` (and dually on the Rx side).
--
-- Each forever-loop is `loop0 body`; each `body` is a `pchoice` menu that
-- pattern-matches the event constructor — needed because `input.id?…d`
-- accepts *any* `d : Data`, which the single-event `⟶₀` cannot express.
-- Connection is now an explicit parameter: each leaf is `Input(id, c)` /
-- `Output(id, c)` for one fixed `id` AND one fixed `c : Conn id`, and the
-- per-connection / per-id replicated interleavings rebuild the whole:
--   Inputs = ||| id : IDs @ (||| c : Conn(id) @ Input(id, c))
-- realised by `interleaveConn` (over `Conn id = Fin (numConns id)`) and
-- `⦀⋆` (over `allIDs`); the empty set ⇒ Skip, the unit of `|||`.
-- `Transmitter`/`Receiver`/`SndAck`/`RcvAck` are single loops handling every
-- `id` via their menu (the CSPm `[] id:IDs @ …`).  All combinators are
-- productive, so no `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ContinueType; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base

module CSP.Examples.Cardano_network.Network
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open import CSP.Examples.Cardano_network.Net p
  using ( Net; Conn; Net-≟
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open Params p using (numConns)

import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op
open Op using (Par⊤; _∥⇘_⇙_; _⦀_; ⦀⋆; ⦀Fin; _∖_; pchoice; Prefix₀; Skip; loop0; chanSet)

------------------------------------------------------------------------
-- A process over the network alphabet, returning the unit on √.
------------------------------------------------------------------------

NetProc : Set₁
NetProc = PTree (Net Data) (ExtI (Net Data)) (⊤ {0ℓ})

-- the visible-offer menu type used by every leaf below
Menu : Set₁
Menu = (at : AnyTypes (Net Data)) → ContinueType at (Maybe NetProc)

------------------------------------------------------------------------
-- Replicated-interleaving combinators (the CSP `|||` over a finite set).
------------------------------------------------------------------------

-- all six protocol ids (for ||| id : IDs @ …)
allIDs : List IDs
allIDs = N2N_ChainSync ∷ N2N_BlockFetch ∷ N2N_TxSubmission
       ∷ N2N_KeepAlive ∷ N2N_LeiosNotify ∷ N2N_LeiosFetch ∷ []

------------------------------------------------------------------------
-- Tx side leaves
------------------------------------------------------------------------

-- Input(id, c): accept input on this id AND connection c, forward as
-- sndmsg, await rcvack, repeat.
Input : (id : IDs) → Conn id → NetProc
Input id c = loop0 (pchoice v)
  where
  v : Menu
  v (_ , input id′ c′) d with id′ ≟ id
  ... | no  _    = nothing
  ... | yes refl with c′ ≟ c
  ...   | yes refl = just (Op.Output (sndmsg id c) d (rcvack id c ⟶₀ Skip))
  ...   | no  _    = nothing
  v _ _ = nothing

-- Transmitter: accept sndmsg on any id, emit tx, repeat ([] id:IDs @ …).
Transmitter : NetProc
Transmitter = loop0 (pchoice v)
  where
  v : Menu
  v (_ , sndmsg id c) d = just (Op.Output (tx id c) d Skip)
  v _ _ = nothing

-- RcvAck: accept ack on any id, emit rcvack, repeat.
RcvAck : NetProc
RcvAck = loop0 (pchoice v)
  where
  v : Menu
  v (_ , ack id c) _ = just (rcvack id c ⟶₀ Skip)
  v _ _ = nothing

------------------------------------------------------------------------
-- Rx side leaves
------------------------------------------------------------------------

-- Output(id, c): accept rcvmsg on this id AND connection c, emit output,
-- emit sndack, repeat.
Output : (id : IDs) → Conn id → NetProc
Output id c = loop0 (pchoice v)
  where
  v : Menu
  v (_ , rcvmsg id′ c′) d with id′ ≟ id
  ... | no  _    = nothing
  ... | yes refl with c′ ≟ c
  ...   | yes refl = just (Op.Output (output id c) d (sndack id c ⟶₀ Skip))
  ...   | no  _    = nothing
  v _ _ = nothing

-- Receiver: accept tx on any id, emit rcvmsg, repeat.
Receiver : NetProc
Receiver = loop0 (pchoice v)
  where
  v : Menu
  v (_ , tx id c) d = just (Op.Output (rcvmsg id c) d Skip)
  v _ _ = nothing

-- SndAck: accept sndack on any id, emit ack, repeat.
SndAck : NetProc
SndAck = loop0 (pchoice v)
  where
  v : Menu
  v (_ , sndack id c) _ = just (ack id c ⟶₀ Skip)
  v _ _ = nothing

------------------------------------------------------------------------
-- Replicated interleavings:
--   InputsId(id) = ||| c : Conn(id) @ Input(id, c)
--   Inputs       = ||| id : IDs @ InputsId(id)
-- (Output side symmetric).  `interleaveConn`/`⦀⋆` realise the replicated
-- `|||`s; the empty set ⇒ Skip, the CSP unit of `|||`.
------------------------------------------------------------------------

InputsId : IDs → NetProc
InputsId id = ⦀Fin (numConns id) (Input id)

Inputs : NetProc
Inputs = ⦀⋆ (map InputsId allIDs)

OutputsId : IDs → NetProc
OutputsId id = ⦀Fin (numConns id) (Output id)

Outputs : NetProc
Outputs = ⦀⋆ (map OutputsId allIDs)

------------------------------------------------------------------------
-- Channel-level synchronisation / hiding sets ( {| … |} in CSPm ).
-- Each predicate selects events purely by their channel (constructor),
-- ignoring the (id , Conn , Data) payload.
------------------------------------------------------------------------

-- {| sndmsg, rcvack |}
csSR : AnyTypes (Net Data) → Set
csSR (_ , sndmsg _ _) = ⊤
csSR (_ , rcvack _ _)   = ⊤
csSR _                  = ⊥

csSR-dec : (at : AnyTypes (Net Data)) → Dec (csSR at)
csSR-dec (_ , sndmsg _ _) = yes tt
csSR-dec (_ , rcvack _ _)   = yes tt
csSR-dec (_ , input _ _)  = no λ ()
csSR-dec (_ , output _ _) = no λ ()
csSR-dec (_ , rcvmsg _ _) = no λ ()
csSR-dec (_ , tx _ _)     = no λ ()
csSR-dec (_ , sndack _ _)   = no λ ()
csSR-dec (_ , ack _ _)      = no λ ()

-- {| rcvmsg, sndack |}
csRS : AnyTypes (Net Data) → Set
csRS (_ , rcvmsg _ _) = ⊤
csRS (_ , sndack _ _)   = ⊤
csRS _                  = ⊥

csRS-dec : (at : AnyTypes (Net Data)) → Dec (csRS at)
csRS-dec (_ , rcvmsg _ _) = yes tt
csRS-dec (_ , sndack _ _)   = yes tt
csRS-dec (_ , input _ _)  = no λ ()
csRS-dec (_ , output _ _) = no λ ()
csRS-dec (_ , sndmsg _ _) = no λ ()
csRS-dec (_ , tx _ _)     = no λ ()
csRS-dec (_ , rcvack _ _)   = no λ ()
csRS-dec (_ , ack _ _)      = no λ ()

-- {| tx, ack |}
csTA : AnyTypes (Net Data) → Set
csTA (_ , tx _ _) = ⊤
csTA (_ , ack _ _)  = ⊤
csTA _              = ⊥

csTA-dec : (at : AnyTypes (Net Data)) → Dec (csTA at)
csTA-dec (_ , tx _ _)     = yes tt
csTA-dec (_ , ack _ _)      = yes tt
csTA-dec (_ , input _ _)  = no λ ()
csTA-dec (_ , output _ _) = no λ ()
csTA-dec (_ , sndmsg _ _) = no λ ()
csTA-dec (_ , rcvmsg _ _) = no λ ()
csTA-dec (_ , sndack _ _)   = no λ ()
csTA-dec (_ , rcvack _ _)   = no λ ()

------------------------------------------------------------------------
-- The two sides and the whole Network.
------------------------------------------------------------------------

TxSide : NetProc
TxSide = (Inputs ∥⇘ chanSet csSR csSR-dec ⇙ (Transmitter ⦀ RcvAck))
           ∖ chanSet csSR csSR-dec

RxSide : NetProc
RxSide = (Outputs ∥⇘ chanSet csRS csRS-dec ⇙ (Receiver ⦀ SndAck))
           ∖ chanSet csRS csRS-dec

Network : NetProc
Network = (TxSide ∥⇘ chanSet csTA csTA-dec ⇙ RxSide)
            ∖ chanSet csTA csTA-dec

------------------------------------------------------------------------
-- The specification of network
-- In CSPM, it is modelled as CopySpec below.
-- Copy(i) = input.i ? t.m.l.d -> output.i ! t.m.l.d -> Copy(i)
-- CopySpec = ||| i:IDs @ Copy(i)
------------------------------------------------------------------------

Copy : (id : IDs) → Conn id → NetProc
Copy id c = loop0 (pchoice v)
  where
  v : Menu
  v (_ , input id′ c′) d with id′ ≟ id
  ... | no  _    = nothing
  ... | yes refl with c′ ≟ c
  ...   | yes refl = just (Op.Output (output id c) d Skip)
  ...   | no  _    = nothing
  v _ _ = nothing

CopysId : IDs → NetProc
CopysId id = ⦀Fin (numConns id) (Copy id)

CopySpec : NetProc
CopySpec = ⦀⋆ (map CopysId allIDs)

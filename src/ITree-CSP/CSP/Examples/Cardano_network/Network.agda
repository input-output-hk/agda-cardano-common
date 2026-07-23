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
--   * CSPm `Connection` becomes the explicit `(l : Link) (d : Dir)` pair
--     threaded through every channel — `Link = Fin numLinks` is the TCP
--     link index and `Dir` (`lo`/`hi`) picks which endpoint initiates that
--     link's instance of the protocol; there is no separate `Conn` type.
--   * CSPm `Time.Mode.Length.Messages` becomes the opaque payload `Data`; the
--     Network only *forwards* it, so this module is generic in `(Data : Set)`
--     with `⦃ DecEq Data ⦄` (the latter feeds `Net-≟` → `CSP.Operators`).
--   * The CSPm ack channels correlate a message with its acknowledgement by
--     `Time`; the refined `Net` ack channels carry `(l, d)` instead, so here
--     the **link/direction pair `(l, d)`** is the correlation token threaded
--     through `input l d id x → sndmsg l d id x → rcvack l d id` (and dually
--     on the Rx side).
--
-- Each forever-loop is `loop0 body`; each `body` is a `pchoice` menu that
-- pattern-matches the event constructor — needed because `input.l.d.id?…x`
-- accepts *any* `x : Data`, which the single-event `⟶₀` cannot express.
-- `(l, d, id)` is now the explicit instance key: each leaf is `Input(l,d,id)`
-- / `Output(l,d,id)` for one fixed link/direction/protocol triple, and the
-- config-driven replicated interleavings rebuild the whole, one live cell
-- per `(d, id)` **configured** on each link by `linkConfig`:
--   Inputs = ||| l : Link @ (||| (d,id) ∈ linkConfig(l) @ Input(l,d,id))
-- realised by `⦀Fin` (over `Link = Fin numLinks`) and `⦀⋆` (over the
-- per-link configured `(Dir × IDs)` list); unconfigured instances
-- contribute no cell and an empty list ⇒ Skip, the unit of `|||`.
-- `Transmitter`/`Receiver`/`SndAck`/`RcvAck` are single loops handling every
-- `(l, d, id)` via their menu (the CSPm `[] id:IDs @ …`).  All combinators
-- are productive, so no `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using (map)
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
  using ( Net; Net-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open Params p using (numLinks; linkConfig)

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
-- Tx side leaves
------------------------------------------------------------------------

-- Input(l, d, id)'s offer menu (hoisted to top level so confinement proofs
-- can name it): accept input l d id for any x, forward as sndmsg, await rcvack.
inputMenu : (l : Link) (d : Dir) (id : IDs) → Menu
inputMenu l d id (_ , input l′ d′ id′) x with l′ ≟ l
... | no  _    = nothing
... | yes refl with d′ ≟ d
...   | no  _    = nothing
...   | yes refl with id′ ≟ id
...     | no  _    = nothing
...     | yes refl = just (Op.Output (sndmsg l d id) x (rcvack l d id ⟶₀ Skip))
inputMenu l d id _ _ = nothing

-- Input(l, d, id): accept input on this link/direction/id, forward as
-- sndmsg, await rcvack, repeat.
Input : (l : Link) (d : Dir) (id : IDs) → NetProc
Input l d id = loop0 (pchoice (inputMenu l d id))

-- Transmitter: accept sndmsg on any (l, d, id), emit tx, repeat.
Transmitter : NetProc
Transmitter = loop0 (pchoice v)
  where
  v : Menu
  v (_ , sndmsg l d id) x = just (Op.Output (tx l d id) x Skip)
  v _ _ = nothing

-- RcvAck: accept ack on any (l, d, id), emit rcvack, repeat.
RcvAck : NetProc
RcvAck = loop0 (pchoice v)
  where
  v : Menu
  v (_ , ack l d id) _ = just (rcvack l d id ⟶₀ Skip)
  v _ _ = nothing

------------------------------------------------------------------------
-- Rx side leaves
------------------------------------------------------------------------

-- Output(l, d, id)'s offer menu (hoisted to top level so confinement proofs
-- can name it): accept rcvmsg l d id for any x, emit output, emit sndack.
outputMenu : (l : Link) (d : Dir) (id : IDs) → Menu
outputMenu l d id (_ , rcvmsg l′ d′ id′) x with l′ ≟ l
... | no  _    = nothing
... | yes refl with d′ ≟ d
...   | no  _    = nothing
...   | yes refl with id′ ≟ id
...     | no  _    = nothing
...     | yes refl = just (Op.Output (output l d id) x (sndack l d id ⟶₀ Skip))
outputMenu l d id _ _ = nothing

-- Output(l, d, id): accept rcvmsg on this link/direction/id, emit output,
-- emit sndack, repeat.
Output : (l : Link) (d : Dir) (id : IDs) → NetProc
Output l d id = loop0 (pchoice (outputMenu l d id))

-- Receiver: accept tx on any (l, d, id), emit rcvmsg, repeat.
Receiver : NetProc
Receiver = loop0 (pchoice v)
  where
  v : Menu
  v (_ , tx l d id) x = just (Op.Output (rcvmsg l d id) x Skip)
  v _ _ = nothing

-- SndAck: accept sndack on any (l, d, id), emit ack, repeat.
SndAck : NetProc
SndAck = loop0 (pchoice v)
  where
  v : Menu
  v (_ , sndack l d id) _ = just (ack l d id ⟶₀ Skip)
  v _ _ = nothing

------------------------------------------------------------------------
-- Config-driven replicated interleavings:
--   Inputs = ||| l : Link @ (||| (d,id) ∈ linkConfig(l) @ Input(l,d,id))
-- (Output side symmetric).  `⦀Fin` ranges over every link, `⦀⋆` ranges
-- over that link's *configured* `(Dir × IDs)` instances only — an
-- unconfigured instance contributes no cell, and `linkConfig l ≡ []` ⇒
-- Skip, the CSP unit of `|||`.
------------------------------------------------------------------------

Inputs : NetProc
Inputs = ⦀Fin numLinks (λ l → ⦀⋆ (map (λ { (d , id) → Input l d id }) (linkConfig l)))

Outputs : NetProc
Outputs = ⦀Fin numLinks (λ l → ⦀⋆ (map (λ { (d , id) → Output l d id }) (linkConfig l)))

------------------------------------------------------------------------
-- Channel-level synchronisation / hiding sets ( {| … |} in CSPm ).
-- Each predicate selects events purely by their channel (constructor),
-- ignoring the (l , d , id , Data) payload.
------------------------------------------------------------------------

-- {| sndmsg, rcvack |}
csSR : AnyTypes (Net Data) → Set
csSR (_ , sndmsg _ _ _) = ⊤
csSR (_ , rcvack _ _ _)   = ⊤
csSR _                  = ⊥

csSR-dec : (at : AnyTypes (Net Data)) → Dec (csSR at)
csSR-dec (_ , sndmsg _ _ _) = yes tt
csSR-dec (_ , rcvack _ _ _)   = yes tt
csSR-dec (_ , input _ _ _)  = no λ ()
csSR-dec (_ , output _ _ _) = no λ ()
csSR-dec (_ , rcvmsg _ _ _) = no λ ()
csSR-dec (_ , tx _ _ _)     = no λ ()
csSR-dec (_ , sndack _ _ _)   = no λ ()
csSR-dec (_ , ack _ _ _)      = no λ ()

-- {| rcvmsg, sndack |}
csRS : AnyTypes (Net Data) → Set
csRS (_ , rcvmsg _ _ _) = ⊤
csRS (_ , sndack _ _ _)   = ⊤
csRS _                  = ⊥

csRS-dec : (at : AnyTypes (Net Data)) → Dec (csRS at)
csRS-dec (_ , rcvmsg _ _ _) = yes tt
csRS-dec (_ , sndack _ _ _)   = yes tt
csRS-dec (_ , input _ _ _)  = no λ ()
csRS-dec (_ , output _ _ _) = no λ ()
csRS-dec (_ , sndmsg _ _ _) = no λ ()
csRS-dec (_ , tx _ _ _)     = no λ ()
csRS-dec (_ , rcvack _ _ _)   = no λ ()
csRS-dec (_ , ack _ _ _)      = no λ ()

-- {| tx, ack |}
csTA : AnyTypes (Net Data) → Set
csTA (_ , tx _ _ _) = ⊤
csTA (_ , ack _ _ _)  = ⊤
csTA _              = ⊥

csTA-dec : (at : AnyTypes (Net Data)) → Dec (csTA at)
csTA-dec (_ , tx _ _ _)     = yes tt
csTA-dec (_ , ack _ _ _)      = yes tt
csTA-dec (_ , input _ _ _)  = no λ ()
csTA-dec (_ , output _ _ _) = no λ ()
csTA-dec (_ , sndmsg _ _ _) = no λ ()
csTA-dec (_ , rcvmsg _ _ _) = no λ ()
csTA-dec (_ , sndack _ _ _)   = no λ ()
csTA-dec (_ , rcvack _ _ _)   = no λ ()

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

-- Copy's offer menu (top-level so the deadlock-free proof can name the residual
-- `Op.Output (output l d id) x Skip`): accept `input l d id` for any `x`, emit it.
copyMenu : (l : Link) (d : Dir) (id : IDs) → Menu
copyMenu l d id (_ , input l′ d′ id′) x with l′ ≟ l
... | no  _    = nothing
... | yes refl with d′ ≟ d
...   | no  _    = nothing
...   | yes refl with id′ ≟ id
...     | no  _    = nothing
...     | yes refl = just (Op.Output (output l d id) x Skip)
copyMenu l d id _ _ = nothing

-- a one-place copy buffer for one mini-protocol instance
Copy : (l : Link) (d : Dir) (id : IDs) → NetProc
Copy l d id = loop0 (pchoice (copyMenu l d id))

-- the copy cells for one link's configured (d, id) instances (unconfigured absent)
linkCopy : Link → NetProc
linkCopy l = ⦀⋆ (map (λ { (d , id) → Copy l d id }) (linkConfig l))

-- the copy medium: every link's bundle, interleaved
CopySpec : NetProc
CopySpec = ⦀Fin numLinks linkCopy

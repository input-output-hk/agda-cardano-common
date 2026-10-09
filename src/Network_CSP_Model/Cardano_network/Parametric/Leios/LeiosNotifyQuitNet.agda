{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeiosNotify GRACEFUL SHUTDOWN OVER THE REAL (BREAKABLE) MEDIUM: what a link break does.
--
-- THE SYSTEM (∀ Params, ∀ link `l`).  The real peers are renamed EXACTLY as `PeersP` does
-- (`LNPclientA l lo` / `LNPserverA l lo`: `sendLNP ↦ input l lo N2N_LeiosNotify`,
-- `receiveLNP ↦ output l lo N2N_LeiosNotify`, `apiLPev ↦ apiLP`, `doneLNP ↦ done`).  In the
-- system (`Node.bundleAtWith`, role convention `mk l d (opposite d)`) the node at the `lo`
-- end of `l` runs the CLIENT of instance `(l , lo , N2N_LeiosNotify)` and the node at the
-- `hi` end runs its SERVER — both named `(l , lo)`.  They are interleaved (they sit in
-- different nodes) and synchronised with the medium on `ioES`:
--     netPair = (cellA l △ (break l ⟶₀ Skip)) [| ioES |] (client ⦀ server)
-- io is left VISIBLE (it makes (i) a plain statement about the trace); api / done / break
-- are open to the environment.
--
-- STEP-0 FINDINGS (recorded here, they shape every statement below):
--  * SHARED CELL.  One instance `(l , d , N2N_LeiosNotify)` owns ONE one-place copy cell
--    `Copy l d N2N_LeiosNotify` (`Network.agda`: input ?x → output !x → loop).  BOTH message
--    directions use it: the client's requests and the server's replies are all written to
--    `input l d LN` and read from `output l d LN`.  Delivery is demultiplexed only by the
--    PAYLOAD — each peer's receive menu accepts only the other side's message kinds (the
--    client: replies / MsgCanceled / MsgDone; the server: RequestNext / MsgQuit).  Since
--    the peers strictly alternate (no pipelining) at most one message is ever in flight,
--    so the one-place cell never blocks a sender.  The cell `(l , opposite d , LN)` belongs
--    to the OTHER LeiosNotify instance on the link (roles swapped) and is not used here.
--  * THE CELL.  `cellA l = renameMap (Copy l lo N2N_LeiosNotify)` is the copy-spec cell.
--    The concrete per-link multiplexer is ≈DR its copy bundle once broken in:
--    `MediumEquivA.breakablePerLink l ne uq : breakableNetLinkA l ≈DR breakableLinkA l`
--    (and `netLinkBreakable≈DR` for the whole medium), whose two hypotheses
--    `linkConfig l ≢ []` and `Unique (linkConfig l)` hold trivially for an LN-only link
--    `linkConfig l ≡ (lo , N2N_LeiosNotify) ∷ []`; for that link `breakableLinkA l` is our
--    medium up to the `⦀`-unit `Copy ⦀ Skip` (not proved here).  On a link carrying more
--    instances the other cells sit on other channels and share only the `break l` event.
--  * BREAK.  `break l` is PER LINK (it interrupts every cell of `l`, both directions, every
--    mini-protocol), it can fire at any moment, it is PERMANENT (the medium becomes `Skip`,
--    i.e. returns), it is not in `ioES` nor in the api set — a free, visible environment
--    event that no peer synchronises on, so the peers are NOT notified.  After it, every
--    io event is refused (`Par` refuses sync-set events against a returned operand).
--  * NO √ WITHOUT A BREAK.  The cell is a `loop0`, it never returns (`MediumEquivA.nr-Copy`,
--    `NoRet`), and `Par` returns only when BOTH operands have.  So the networked pair can
--    never reach √ unless the link is broken — even after a complete Quit/Done handshake
--    the peers have returned but the cell still offers `input`: the pair is stuck there.
--
-- THE RESULTS (§5, §6):
--  (i)   `noIoAfterBreak` / `noIoAfterBreak-tr`: in every trace, after a `break l` NO io
--        event (`input`/`output`, ANY link and ANY id) occurs.
--  (ii)  `earlyBreak-no√`: if `break l` fires in a reachable state in which the peer pair is
--        NOT already finished (`¬ PeersDone`: no decomposition with both peers returned),
--        then √ is unreachable from there — a break during LeiosNotify forfeits graceful
--        shutdown.  (Informally the remainder can do only a few api / done events before it is
--        stuck; that bound is NOT proved here — only that every later step is io-free (i).)
--  (iii) `no√WithoutBreak`: every √ of the networked pair is preceded by `break l` in its
--        trace (the cell never returns).  `graceful√`: a concrete run with the full
--        handshake — RequestNext, MsgCanceled, Quit, the server's done, MsgDone — then
--        `break l`, then √.  So √ is reachable ONLY as "complete the handshake, then close
--        the link"; closing the link earlier leaves the peers stuck.
-- All proofs are constructive (no `Classical`, no postulate).
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosNotifyQuitNet (p : Params) where

open import Level using (0ℓ; Level)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import Class.DecEq.Instances as DecEqI

open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p
open Params p using (time₀; length₀)

-- the direct-pairing development: the client abstraction `CPos`/`CStp`, step helpers
import Cardano_network.Parametric.Leios.LeiosNotifyQuit p as LQ
-- the server's step views (generic in the direction)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLNP p
  using (snd; siNext; siQuit; sIdleV; sbCan; sbAnn; sbOff; sbTxs; sbVote; sBusyV; sqDone; sQuitV)
-- the real peers' rename into the system alphabet
open import Cardano_network.Parametric.Leios.PeersP p using (ιLNP; ιLNP⁻¹; ιLNP-linv)
open import Cardano_network.NetCommon p using (ιNet; ιNet⁻¹; ιNet-linv; ioSet; ioES)
open import Cardano_network.Network p Payload using (Copy)
-- the copy medium is non-terminating
open import Cardano_network.MediumEquivA p using (nr-Copy)

-- a fixed payload (only to instantiate `NetworkDeadlockFree`'s witness parameter)
d₀ : Payload
d₀ = time₀ , FromInitiator , length₀ , leiosNotifyP MsgLNPRequestNext

-- the copy cell's named residuals and their step equations
open import Cardano_network.NetworkVerification.NetworkDeadlockFree p Payload d₀
  using (copy-A; copy-B; copy-C; probe-A; probe-A-off; probe-B; probe-B-off; probe-C)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Par; Par⊤; _∥⇘_⇙_; _⦀_; _△_; Prefix₀; Prefix-cont; Skip; EventSet; ∅ES; viewV)
open EventSet
import CSP.Operators LNPEv-≟ as OL

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as L1
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as L0
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)

open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
  using (τL; τR; evSync; evL; evR; evBoth; ev√; Par-τ-elim; Par-ev-elim; Par-force-ret-inv; fPar-rr; viewV-ev)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-τ-L; Par-τ-R; Par-sync; Par-soloL; Par-soloR)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt (Net_Api-≟ {Payload})
  using (△τP; △τQ; △τQret; △τ⊓P; △τ⊓Q; △-τ-elim; △evP; △evQ; △evPQ; △-ev-elim; force-△-mt; ret-no-τ)
open import CSP.Laws.FD.InterruptFD (Net_Api-≟ {Payload}) using (△-merge-noP; △-merge-noQ; △-τ-lift-P)
open import CSP.Laws.Traces.TraceLawsExtChoice (Net_Api-≟ {Payload}) using (NonRet)
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload}) using (OffersOnly; NoRet)
open import CSP.Laws.DivFree.Loop LNPEv-≟ using (iter-ev-elim)
import CSP.Rename {E₁ = LNPEv} {E₂ = Net_Api Payload} ιLNP ιLNP⁻¹ ιLNP-linv as RnP
import CSP.Laws.Traces.RenameDeadlock {E₁ = LNPEv} {E₂ = Net_Api Payload} ιLNP ιLNP⁻¹ ιLNP-linv as RP
import CSP.Laws.Traces.RenameDeadlock {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv as RN
import CSP.Laws.Bisim.RenameOffers (Net-≟ {Payload}) (Net_Api-≟ {Payload}) ιNet ιNet⁻¹ ιNet-linv as OM

------------------------------------------------------------------------
-- §0  Small Bool facts and event classifiers (no link)
------------------------------------------------------------------------

-- the process type of the networked pair (the one `Parametric.Node` uses)
Proc : Set₁
Proc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- true and false differ
t≢f : true ≡ false → ⊥
t≢f ()

-- a Bool that cannot be true (its truth would yield an impossible `P`) is false
bool-false : ∀ {ℓ} {b : Bool} {P : Set ℓ} → (b ≡ true → P) → ¬ P → b ≡ false
bool-false {b = false} _ _  = refl
bool-false {b = true} f ¬p = ⊥-elim (¬p (f refl))

-- a false left conjunct makes the conjunction false
∧-fl : ∀ {a b : Bool} → a ≡ false → a ∧ b ≡ false
∧-fl refl = refl

-- a false right conjunct makes the conjunction false
∧-fr : ∀ {a b : Bool} → b ≡ false → a ∧ b ≡ false
∧-fr {true}  refl = refl
∧-fr {false} _    = refl

-- a true conjunction has both conjuncts true
∧-tt : ∀ {a b : Bool} → a ∧ b ≡ true → a ≡ true × b ≡ true
∧-tt {true} {true} _ = refl , refl
∧-tt {true} {false} ()
∧-tt {false} ()

-- the eight wire channels of the medium (on any link)
isWire : ∀ {A} → Net_Api Payload A → Bool
isWire (input  _ _ _) = true
isWire (output _ _ _) = true
isWire (sndmsg _ _ _) = true
isWire (rcvmsg _ _ _) = true
isWire (tx     _ _ _) = true
isWire (sndack _ _ _) = true
isWire (rcvack _ _ _) = true
isWire (ack    _ _ _) = true
isWire _              = false

-- the channels a renamed LeiosNotify peer uses
isPeer : ∀ {A} → Net_Api Payload A → Bool
isPeer (input  _ _ _) = true
isPeer (output _ _ _) = true
isPeer (apiLP  _ _ _) = true
isPeer (done   _ _ _) = true
isPeer _              = false

-- the medium's alphabet before a break: the wire channels
WireA : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Set
WireA at _ = isWire (proj₂ at) ≡ true

-- an event both on the wire and on a peer channel is an io event
wp-io : ∀ {A} (e : Net_Api Payload A) → isWire e ≡ true → isPeer e ≡ true → ioSet (A , e)
wp-io (input  _ _ _) _ _ = tt
wp-io (output _ _ _) _ _ = tt
wp-io (sndmsg _ _ _) _ ()
wp-io (rcvmsg _ _ _) _ ()
wp-io (tx     _ _ _) _ ()
wp-io (sndack _ _ _) _ ()
wp-io (rcvack _ _ _) _ ()
wp-io (ack    _ _ _) _ ()
wp-io (done   _ _ _) () _
wp-io (apiCS  _ _ _) () _
wp-io (apiBF  _ _ _) () _
wp-io (apiTS  _ _ _) () _
wp-io (apiKA  _ _ _) () _
wp-io (apiLN  _ _ _) () _
wp-io (apiLF  _ _ _) () _
wp-io (apiLP  _ _ _) () _
wp-io (store  _ _ _) () _
wp-io (env    _ _ _) () _
wp-io (break  _)     () _

-- whether a LeiosNotify message is an initiator (client-sent) message
isInit : MessageLeiosNotifyP → Bool
isInit MsgLNPRequestNext = true
isInit MsgLNPQuit        = true
isInit _                 = false

-- whether an api tag is used by the LeiosNotify CLIENT
cliTag : ApiLPTag → Bool
cliTag lnpSendRequestNext       = true
cliTag lnpSendDone              = true
cliTag lnpRecvBlockAnnouncement = true
cliTag lnpRecvBlockOffer        = true
cliTag lnpRecvBlockTxsOffer     = true
cliTag lnpRecvVotes             = true
cliTag _                        = false

-- which peer of the pair can perform a (renamed) event: true = client, false = server
owner : ∀ {A} → Net_Api Payload A → A → Bool
owner (input  _ _ _) (_ , _ , _ , leiosNotifyP m) = isInit m
owner (output _ _ _) (_ , _ , _ , leiosNotifyP m) = not (isInit m)
owner (apiLP  _ _ m) _                            = cliTag m
owner _              _                            = false

-- the owner of a source (LNPEv) event, read through the rename
ownL : L1.Event → Bool
ownL (L1.evLabel A e a) = owner (ιLNP e) a

-- a source event is an io event once renamed (a wire send / receive)
IoL : L1.Event → Set
IoL (L1.evLabel A e a) = ioSet (A , ιLNP e)

-- every renamed peer event lands on a peer channel
peerι : ∀ {A} (e : LNPEv A) → isPeer (ιLNP e) ≡ true
peerι (sendLNP _ _)    = refl
peerι (receiveLNP _ _) = refl
peerι (apiLPev _ _ _)  = refl
peerι (doneLNP _ _)    = refl

-- a renamed event IS the `ιLNP`-image of its source, so any property of the image holds of it
visImg : (P : ∀ {A : Set} → Net_Api Payload A → A → Set) (bt : AnyTypes (Net_Api Payload)) (b : proj₁ bt)
         (at : AnyTypes LNPEv) (a : proj₁ at)
       → RnP.ι-vis-inv bt b ≡ just (at , a) → P (ιLNP (proj₂ at)) a → P (proj₂ bt) b
visImg P (_ , input  _ _ N2N_LeiosNotify)  _ _ _ refl x = x
visImg P (_ , input  _ _ N2N_ChainSync)    _ _ _ () _
visImg P (_ , input  _ _ N2N_BlockFetch)   _ _ _ () _
visImg P (_ , input  _ _ N2N_TxSubmission) _ _ _ () _
visImg P (_ , input  _ _ N2N_KeepAlive)    _ _ _ () _
visImg P (_ , input  _ _ N2N_LeiosFetch)   _ _ _ () _
visImg P (_ , output _ _ N2N_LeiosNotify)  _ _ _ refl x = x
visImg P (_ , output _ _ N2N_ChainSync)    _ _ _ () _
visImg P (_ , output _ _ N2N_BlockFetch)   _ _ _ () _
visImg P (_ , output _ _ N2N_TxSubmission) _ _ _ () _
visImg P (_ , output _ _ N2N_KeepAlive)    _ _ _ () _
visImg P (_ , output _ _ N2N_LeiosFetch)   _ _ _ () _
visImg P (_ , done   _ _ N2N_LeiosNotify)  _ _ _ refl x = x
visImg P (_ , done   _ _ N2N_ChainSync)    _ _ _ () _
visImg P (_ , done   _ _ N2N_BlockFetch)   _ _ _ () _
visImg P (_ , done   _ _ N2N_TxSubmission) _ _ _ () _
visImg P (_ , done   _ _ N2N_KeepAlive)    _ _ _ () _
visImg P (_ , done   _ _ N2N_LeiosFetch)   _ _ _ () _
visImg P (_ , apiLP  _ _ _)                _ _ _ refl x = x
visImg P (_ , sndmsg _ _ _) _ _ _ () _
visImg P (_ , rcvmsg _ _ _) _ _ _ () _
visImg P (_ , tx     _ _ _) _ _ _ () _
visImg P (_ , sndack _ _ _) _ _ _ () _
visImg P (_ , rcvack _ _ _) _ _ _ () _
visImg P (_ , ack    _ _ _) _ _ _ () _
visImg P (_ , apiCS  _ _ _) _ _ _ () _
visImg P (_ , apiBF  _ _ _) _ _ _ () _
visImg P (_ , apiTS  _ _ _) _ _ _ () _
visImg P (_ , apiKA  _ _ _) _ _ _ () _
visImg P (_ , apiLN  _ _ _) _ _ _ () _
visImg P (_ , apiLF  _ _ _) _ _ _ () _
visImg P (_ , store  _ _ _) _ _ _ () _
visImg P (_ , env    _ _ _) _ _ _ () _
visImg P (_ , break  _)     _ _ _ () _

-- the renamed copy cell only ever offers wire channels
cellImg : ∀ bt b at a → OM.ι-vis-inv bt b ≡ just (at , a) → WireA bt b
cellImg (_ , input  _ _ _) _ _ _ _ = refl
cellImg (_ , output _ _ _) _ _ _ _ = refl
cellImg (_ , sndmsg _ _ _) _ _ _ _ = refl
cellImg (_ , rcvmsg _ _ _) _ _ _ _ = refl
cellImg (_ , tx     _ _ _) _ _ _ _ = refl
cellImg (_ , sndack _ _ _) _ _ _ _ = refl
cellImg (_ , rcvack _ _ _) _ _ _ _ = refl
cellImg (_ , ack    _ _ _) _ _ _ _ = refl
cellImg (_ , done   _ _ _) _ _ _ ()
cellImg (_ , apiCS  _ _ _) _ _ _ ()
cellImg (_ , apiBF  _ _ _) _ _ _ ()
cellImg (_ , apiTS  _ _ _) _ _ _ ()
cellImg (_ , apiKA  _ _ _) _ _ _ ()
cellImg (_ , apiLN  _ _ _) _ _ _ ()
cellImg (_ , apiLF  _ _ _) _ _ _ ()
cellImg (_ , apiLP  _ _ _) _ _ _ ()
cellImg (_ , store  _ _ _) _ _ _ ()
cellImg (_ , env    _ _ _) _ _ _ ()
cellImg (_ , break  _)     _ _ _ ()

-- the server's replies are not initiator messages
repNotInit : ∀ {l} (r : LQ.Rep l) → isInit (LQ.repM l r) ≡ false
repNotInit (LQ.rA _)   = refl
repNotInit (LQ.rO _ _) = refl
repNotInit (LQ.rT _)   = refl
repNotInit (LQ.rV _)   = refl
repNotInit LQ.rC       = refl

-- a step of a returned tree is never visible
retNoEv : ∀ {t t′ : Proc} {x} → PTree.force t ≡ ret tt → t ─[ ev (evl x) ]─► t′ → ⊥
retNoEv eq (sVis eq′ _) with trans (sym eq) eq′
... | ()

-- a √-free run over `s₁ ++ e ∷ s₂` passes through an `e`-step
splitRun : ∀ {t W : Proc} (s₁ : List Event) {e s₂}
         → t ⟹∖√⟨ s₁ ++ e ∷ s₂ ⟩ W
         → Σ[ W₁ ∈ Proc ] Σ[ W₂ ∈ Proc ] (t ⟹∖√⟨ s₁ ⟩ W₁ × W₁ ─[ ev (evl e) ]─► W₂ × W₂ ⟹∖√⟨ s₂ ⟩ W)
splitRun [] (∖√-τ st r) with splitRun [] r
... | W₁ , W₂ , r₁ , b , r₂ = W₁ , W₂ , ∖√-τ st r₁ , b , r₂
splitRun [] (∖√-ev st r) = _ , _ , ∖√-refl , st , r
splitRun (x ∷ s₁) (∖√-τ st r) with splitRun (x ∷ s₁) r
... | W₁ , W₂ , r₁ , b , r₂ = W₁ , W₂ , ∖√-τ st r₁ , b , r₂
splitRun (x ∷ s₁) (∖√-ev st r) with splitRun s₁ r
... | W₁ , W₂ , r₁ , b , r₂ = W₁ , W₂ , ∖√-ev st r₁ , b , r₂

-- an event that is not an io event
NoIo : Event → Set
NoIo x = ¬ ioSet (Event.A x , Event.e x)

------------------------------------------------------------------------
-- everything below is for one link `l`
------------------------------------------------------------------------

module _ (l : Link) where

  ------------------------------------------------------------------------
  -- §1  The networked pair
  ------------------------------------------------------------------------

  -- the renamed client / server trees (PeersP's rename, as a function of the source tree)
  RC : LQ.Tree → Proc
  RC = RnP.renameMap

  -- the break handler: `break l`, then terminate
  brk : Proc
  brk = Prefix₀ (break l) Skip

  -- the `break l` event
  brkEv : Event
  brkEv = evLabel _ (break l) U.tt

  -- the copy cell of instance (l , lo , N2N_LeiosNotify), renamed into the system alphabet
  cellA : Proc
  cellA = OM.renameMap (Copy l lo N2N_LeiosNotify)

  -- the breakable medium of the instance
  medA : Proc
  medA = cellA △ brk

  -- THE NETWORKED PAIR: medium against the interleaved real peers, synchronised on io
  netPair : Proc
  netPair = medA ∥⇘ ioES ⇙ (RC (LNPclientStClient l lo) ⦀ RC (LNPserverStClient l lo))

  -- the pair has finished: some decomposition shows both peers returned
  PeersDone : Proc → Set₁
  PeersDone W = Σ[ m ∈ Proc ] Σ[ c ∈ Proc ] Σ[ s ∈ Proc ]
                  (W ≡ Par⊤ ioES m (Par⊤ ∅ES c s) × PTree.force c ≡ ret tt × PTree.force s ≡ ret tt)

  ------------------------------------------------------------------------
  -- §2  The medium
  ------------------------------------------------------------------------

  -- a live medium: a wire-confined, non-terminating cell state under the break interrupt
  LiveM : Proc → Set₁
  LiveM m = Σ[ x ∈ Proc ] (m ≡ (x △ brk) × OffersOnly WireA x × NoRet x)

  -- the confinement of a cell state (wire alphabet, never returns)
  MedOK : Proc → Set₁
  MedOK x = OffersOnly WireA x × NoRet x

  -- a cell step keeps the confinement
  mok-step : ∀ {x x′ lb} → MedOK x → x ─[ lb ]─► x′ → MedOK x′
  mok-step (oo , nr) st = OffersOnly.step oo st , NoRet.stepNR nr st

  -- the initial cell is confined: the rename's image is the wire, and `Copy` is a loop
  mok₀ : MedOK cellA
  mok₀ = OM.OffersOnly-renameMap-image {P = Copy l lo N2N_LeiosNotify} cellImg
       , OM.NoRet-renameMap (nr-Copy l lo N2N_LeiosNotify)

  -- the break handler makes no τ
  brkNoτ : ∀ {t} → brk ─[ τ ]─► t → ⊥
  brkNoτ (sSil ())
  brkNoτ (sTau refl ())

  -- the break handler's only visible step is `break l`, into `Skip`
  brkStep : ∀ {x t} → brk ─[ ev (evl x) ]─► t → x ≡ brkEv × t ≡ Skip
  brkStep (sVis {at = at} {a = a} refl br) with Net_Api-≟ (_ , break l) at
  ... | yes refl = refl , sym (just-injective br)
  ... | no _ with br
  ...   | ()

  -- the break handler offers `break l` (into `Skip`)
  brkOff : Prefix-cont (break l) (λ _ → Skip) (U.⊤ , break l) U.tt ≡ just (Skip {0ℓ})
  brkOff rewrite LQ.≟-refl l = refl

  -- a wire event is not `break l`
  wireNotBrk : ∀ {x} → x ≡ brkEv → isWire (Event.e x) ≡ true → ⊥
  wireNotBrk refl ()

  -- `break l` is not a peer event
  brkNotPeer : ∀ {x} → x ≡ brkEv → isPeer (Event.e x) ≡ true → ⊥
  brkNotPeer refl ()

  -- the break handler offers no wire event
  brkNoWire : ∀ {X} {e : Net_Api Payload X} {a : X} → isWire e ≡ true
            → viewV (PTree.force brk) (X , e) a ≡ nothing
  brkNoWire {X} {e} {a} w with viewV (PTree.force brk) (X , e) a in eq
  ... | nothing = refl
  ... | just _  = ⊥-elim (wireNotBrk (proj₁ (brkStep (viewV-ev {P = brk} refl eq))) w)

  -- the interrupt never terminates while the cell is live (`△` is always a react node)
  △noRet : ∀ x {r} → PTree.force (x △ brk) ≡ ret r → ⊥
  △noRet x eq with △-ev-elim x brk (sRet eq)
  ... | ()

  -- a τ of the live medium: the cell moves, still under the interrupt
  mτ : ∀ {m m′} → LiveM m → m ─[ τ ]─► m′ → LiveM m′
  mτ (x , refl , oo , nr) st with △-τ-elim x brk st
  ... | △τP st′  = _ , refl , OffersOnly.step oo st′ , NoRet.stepNR nr st′
  ... | △τQ st′  = ⊥-elim (brkNoτ st′)
  ... | △τQret ()
  ... | △τ⊓P eq  = ⊥-elim (subst NonRet eq (NoRet.nowNR nr))
  ... | △τ⊓Q eq  = ⊥-elim (subst NonRet eq (NoRet.nowNR nr))

  -- a visible step of the live medium: a wire event (still live), or `break l` into `Skip`
  mE : ∀ {m m′ x} → LiveM m → m ─[ ev (evl x) ]─► m′
     → (LiveM m′ × isWire (Event.e x) ≡ true) ⊎ (x ≡ brkEv × m′ ≡ Skip)
  mE (y , refl , oo , nr) st with △-ev-elim y brk st
  ... | △evP st′      = inj₁ ((_ , refl , OffersOnly.step oo st′ , NoRet.stepNR nr st′) , OffersOnly.now oo st′)
  ... | △evQ st′      = inj₂ (brkStep st′)
  ... | △evPQ st₁ st₂ = ⊥-elim (wireNotBrk (proj₁ (brkStep st₂)) (OffersOnly.now oo st₁))

  -- the live medium does not offer a non-wire peer event
  nMx : ∀ {x X} {e : Net_Api Payload X} {a : X} → MedOK x → isWire e ≡ false → isPeer e ≡ true
      → viewV (PTree.force (x △ brk)) (X , e) a ≡ nothing
  nMx {x} {X} {e} {a} (oo , nr) nw pe with viewV (PTree.force (x △ brk)) (X , e) a in eq
  ... | nothing = refl
  ... | just _ with mE (x , refl , oo , nr) (viewV-ev {P = x △ brk} refl eq)
  ...   | inj₁ (_ , w) = ⊥-elim (t≢f (trans (sym w) nw))
  ...   | inj₂ (b , _) = ⊥-elim (brkNotPeer b pe)

  -- a wire step of the cell is a step of the live medium
  mStepW : ∀ {x x′ X} {e : Net_Api Payload X} {a : X}
         → x ─[ ev (evl (evLabel X e a)) ]─► x′ → isWire e ≡ true
         → (x △ brk) ─[ ev (evl (evLabel X e a)) ]─► (x′ △ brk)
  mStepW {x} (sVis {v = v} {τc = τc} eqx brx) w =
    sVis (force-△-mt {P = x} {Q = brk} eqx refl U.tt U.tt)
         (△-merge-noQ {Q = brk} {nP = react v τc} {nQ = PTree.force brk} brx (brkNoWire w))

  -- the break fires from any confined cell state, leaving `Skip`
  mBrk : ∀ {x} → MedOK x → (x △ brk) ─[ ev (evl brkEv) ]─► Skip
  mBrk {x} (oo , nr) =
    sVis (force-△-mt {P = x} {Q = brk} refl refl (NoRet.nowNR nr) U.tt)
         (△-merge-noP {Q = brk} {Q₁ = Skip} {vQ = Prefix-cont (break l) (λ _ → Skip)} {τcQ = Op.∅t}
                      {nP = PTree.force x} vp brkOff)
    where
    -- the cell does not offer `break l`
    vp : viewV (PTree.force x) (U.⊤ , break l) U.tt ≡ nothing
    vp with viewV (PTree.force x) (U.⊤ , break l) U.tt in eq
    ... | nothing = refl
    ... | just _ with OffersOnly.now oo (viewV-ev {P = x} refl eq)
    ...   | ()

  ------------------------------------------------------------------------
  -- §3  The peers: the client by `LQ.CPos`, the server (at `(l , lo)`) by `SPos`
  ------------------------------------------------------------------------

  -- the client phase has ended
  isEC : LQ.CS l → Bool
  isEC LQ.cE = true
  isEC _     = false

  -- the server phase has ended
  isES : LQ.SS l → Bool
  isES LQ.sE = true
  isES _     = false

  -- every visible client step is the client's own event
  cOwn : ∀ {σ ω σ′} → LQ.CStp l σ (LQ.ev′ ω) σ′ → ownL (LQ.⌜_⌝ l ω) ≡ true
  cOwn (LQ.cRN _)   = refl
  cOwn (LQ.cQi _)   = refl
  cOwn LQ.cSR       = refl
  cOwn LQ.cSQ       = refl
  cOwn (LQ.cRA _)   = refl
  cOwn (LQ.cRO _ _) = refl
  cOwn (LQ.cRT _)   = refl
  cOwn (LQ.cRV _)   = refl
  cOwn LQ.cRC       = refl
  cOwn (LQ.cDA _)   = refl
  cOwn (LQ.cDO _ _) = refl
  cOwn (LQ.cDT _)   = refl
  cOwn (LQ.cDV _)   = refl
  cOwn LQ.cDn       = refl

  -- the client ends only by an io step (receiving MsgDone)
  cEnd : ∀ {σ ω σ′} → LQ.CStp l σ (LQ.ev′ ω) σ′ → isEC (proj₁ σ′) ≡ true → IoL (LQ.⌜_⌝ l ω)
  cEnd LQ.cDn       _ = tt
  cEnd (LQ.cRN _)   ()
  cEnd (LQ.cQi _)   ()
  cEnd LQ.cSR       ()
  cEnd LQ.cSQ       ()
  cEnd (LQ.cRA _)   ()
  cEnd (LQ.cRO _ _) ()
  cEnd (LQ.cRT _)   ()
  cEnd (LQ.cRV _)   ()
  cEnd LQ.cRC       ()
  cEnd (LQ.cDA _)   ()
  cEnd (LQ.cDO _ _) ()
  cEnd (LQ.cDT _)   ()
  cEnd (LQ.cDV _)   ()

  -- a client τ is a loop-back, never into the end
  cτEnd : ∀ {σ σ′} → LQ.CStp l σ LQ.τ′ σ′ → isEC (proj₁ σ′) ≡ false
  cτEnd LQ.cτI = refl
  cτEnd LQ.cτB = refl
  cτEnd LQ.cτQ = refl

  -- a terminated client phase is the end
  cfinE : ∀ σ → LQ.CFin l σ → isEC (proj₁ σ) ≡ true
  cfinE (LQ.cE , _)   _  = refl
  cfinE (LQ.cI , _)   ()
  cfinE (LQ.cB , _)   ()
  cfinE (LQ.cQ , _)   ()
  cfinE (LQ.cR , _)   ()
  cfinE (LQ.cS , _)   ()
  cfinE (LQ.cD _ , _) ()

  -- the end phase is terminated
  ecFin : ∀ σ → isEC (proj₁ σ) ≡ true → LQ.CFin l σ
  ecFin (LQ.cE , _)   _  = U.tt
  ecFin (LQ.cI , _)   ()
  ecFin (LQ.cB , _)   ()
  ecFin (LQ.cQ , _)   ()
  ecFin (LQ.cR , _)   ()
  ecFin (LQ.cS , _)   ()
  ecFin (LQ.cD _ , _) ()

  -- the server's loop body at `(l , lo)`
  ksL : LNPState → PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)
  ksL = serverStepP l lo

  -- where a server tree (at `(l , lo)`) is; the flag marks a pending loop-back τ
  data SPos : LQ.SS l × Bool → LQ.Tree → Set₁ where
    spI  : SPos (LQ.sI , false) (OL.iter ksL stIdle)
    spB  : SPos (LQ.sB , false) (OL.iter ksL stBusy)
    spQ  : SPos (LQ.sQ , false) (OL.iter ksL stQuit)
    spI′ : SPos (LQ.sI , true) (OL.iter-bind (OL.Ret (inj₁ stIdle)) ksL)
    spB′ : SPos (LQ.sB , true) (OL.iter-bind (OL.Ret (inj₁ stBusy)) ksL)
    spQ′ : SPos (LQ.sQ , true) (OL.iter-bind (OL.Ret (inj₁ stQuit)) ksL)
    spN  : ∀ r → SPos (LQ.sN r , false) (OL.iter-bind (snd l lo FromResponder (LQ.repM l r) stIdle) ksL)
    spD  : SPos (LQ.sD , false)
                (OL.iter-bind (OL.Output (sendLNP l lo) (LQ.pay l FromResponder MsgLNPDone) (OL.Ret (inj₂ tt))) ksL)
    spE  : SPos (LQ.sE , false) (OL.iter-bind (OL.Ret (inj₂ tt)) ksL)

  -- a server τ is a loop-back, never into the end
  sτ₀ : ∀ {σ s s′} → SPos σ s → s L1.─[ L1.τ ]─► s′ → Σ[ σ′ ∈ LQ.SS l × Bool ] (SPos σ′ s′ × isES (proj₁ σ′) ≡ false)
  sτ₀ spI st = ⊥-elim (LQ.IterNoτ.τ✗ LQ.pchNoτ (λ ()) st)
  sτ₀ spB st = ⊥-elim (LQ.IterNoτ.τ✗ LQ.pchNoτ (λ ()) st)
  sτ₀ spQ st = ⊥-elim (LQ.IterNoτ.τ✗ LQ.pchNoτ (λ ()) st)
  sτ₀ spI′ (L1.sSil refl) = _ , spI , refl
  sτ₀ spB′ (L1.sSil refl) = _ , spB , refl
  sτ₀ spQ′ (L1.sSil refl) = _ , spQ , refl
  sτ₀ spI′ (L1.sTau () _)
  sτ₀ spB′ (L1.sTau () _)
  sτ₀ spQ′ (L1.sTau () _)
  sτ₀ (spN _) st = ⊥-elim (LQ.IterNoτ.τ✗ LQ.outNoτ (λ ()) st)
  sτ₀ spD st = ⊥-elim (LQ.IterNoτ.τ✗ LQ.outNoτ (λ ()) st)
  sτ₀ spE (L1.sSil ())
  sτ₀ spE (L1.sTau () _)

  -- a visible server step: the server's own event, ending the server only if it is io
  sE₀ : ∀ {σ s s′ x} → SPos σ s → s L1.─[ L1.ev (L1.evl x) ]─► s′
      → Σ[ σ′ ∈ LQ.SS l × Bool ] (SPos σ′ s′ × ownL x ≡ false × (isES (proj₁ σ′) ≡ true → IoL x))
  sE₀ spI st with iter-ev-elim (ksL stIdle) ksL st
  ... | _ , st′ , refl with sIdleV st′
  ...   | siNext = _ , spB′ , refl , λ ()
  ...   | siQuit = _ , spQ′ , refl , λ ()
  sE₀ spB st with iter-ev-elim (ksL stBusy) ksL st
  ... | _ , st′ , refl with sBusyV st′
  ...   | sbCan _    = _ , spN LQ.rC , refl , λ ()
  ...   | sbAnn h    = _ , spN (LQ.rA h) , refl , λ ()
  ...   | sbOff q sz = _ , spN (LQ.rO q sz) , refl , λ ()
  ...   | sbTxs q    = _ , spN (LQ.rT q) , refl , λ ()
  ...   | sbVote vs  = _ , spN (LQ.rV vs) , refl , λ ()
  sE₀ spQ st with iter-ev-elim (ksL stQuit) ksL st
  ... | _ , st′ , refl with sQuitV st′
  ...   | sqDone _ = _ , spD , refl , λ ()
  sE₀ spI′ (L1.sVis () _)
  sE₀ spB′ (L1.sVis () _)
  sE₀ spQ′ (L1.sVis () _)
  sE₀ (spN r) st with iter-ev-elim (snd l lo FromResponder (LQ.repM l r) stIdle) ksL st
  ... | _ , st′ , refl with LQ.outI st′
  ...   | refl , refl = _ , spI′ , repNotInit r , λ ()
  sE₀ spD st with iter-ev-elim (OL.Output (sendLNP l lo) (LQ.pay l FromResponder MsgLNPDone) (OL.Ret (inj₂ tt))) ksL st
  ... | _ , st′ , refl with LQ.outI st′
  ...   | refl , refl = _ , spE , refl , λ _ → tt
  sE₀ spE (L1.sVis () _)

  -- a server tree returns only at the end
  sR₀ : ∀ {σ s r} → SPos σ s → PTree.force s ≡ ret r → isES (proj₁ σ) ≡ true
  sR₀ spE     _  = refl
  sR₀ spI     ()
  sR₀ spB     ()
  sR₀ spQ     ()
  sR₀ spI′    ()
  sR₀ spB′    ()
  sR₀ spQ′    ()
  sR₀ (spN _) ()
  sR₀ spD     ()

  -- the server at its end has returned
  sRetE : ∀ {σ s} → SPos σ s → isES (proj₁ σ) ≡ true → PTree.force s ≡ ret tt
  sRetE spE     _  = refl
  sRetE spI     ()
  sRetE spB     ()
  sRetE spQ     ()
  sRetE spI′    ()
  sRetE spB′    ()
  sRetE spQ′    ()
  sRetE (spN _) ()
  sRetE spD     ()

  ------------------------------------------------------------------------
  -- the renamed peers, step by step
  ------------------------------------------------------------------------

  -- a visible step of the renamed client: new phase, the client's event on a peer channel,
  -- ending the client only if io
  rcE : ∀ {σ c W X} {e : Net_Api Payload X} {a : X} → LQ.CPos l σ c → RC c ─[ ev (evl (evLabel X e a)) ]─► W
      → Σ[ c′ ∈ LQ.Tree ] Σ[ σ′ ∈ LQ.CS l × Bool ]
          (W ≡ RC c′ × LQ.CPos l σ′ c′ × owner e a ≡ true × isPeer e ≡ true × (isEC (proj₁ σ′) ≡ true → ioSet (X , e)))
  rcE {c = c} pc st with RP.ren-ev-inv {inv = RnP.ι-vis-inv} {P = c} st
  ... | inj₂ (_ , () , _)
  ... | inj₁ (at , a′ , bt , b , c₁ , cst , eqi , refl , refl) with LQ.cElimE l pc cst
  ...   | ω , σ′ , eω , stp , pc′ =
          c₁ , σ′ , refl , pc′
        , visImg (λ e x → owner e x ≡ true) bt b at a′ eqi (subst (λ z → ownL z ≡ true) (sym eω) (cOwn stp))
        , visImg (λ e _ → isPeer e ≡ true) bt b at a′ eqi (peerι (proj₂ at))
        , λ h → visImg (λ {A} e _ → ioSet (A , e)) bt b at a′ eqi (subst IoL (sym eω) (cEnd stp h))

  -- a τ of the renamed client: a loop-back
  rcτ : ∀ {σ c W} → LQ.CPos l σ c → RC c ─[ τ ]─► W
      → Σ[ c′ ∈ LQ.Tree ] Σ[ σ′ ∈ LQ.CS l × Bool ] (W ≡ RC c′ × LQ.CPos l σ′ c′ × isEC (proj₁ σ′) ≡ false)
  rcτ {c = c} pc st with RP.ren-τ-inv {inv = RnP.ι-vis-inv} {P = c} st
  ... | c₁ , cst , refl with LQ.cElimτ l pc cst
  ...   | σ′ , stp , pc′ = c₁ , σ′ , refl , pc′ , cτEnd stp

  -- the renamed client returns only at its end
  rcR : ∀ {σ c r} → LQ.CPos l σ c → PTree.force (RC c) ≡ ret r → isEC (proj₁ σ) ≡ true
  rcR {σ} {c} pc eq = cfinE σ (LQ.cElimR l pc (RP.force-ren-ret-inv {inv = RnP.ι-vis-inv} {P = c} eq))

  -- a visible step of the renamed server: new phase, the server's event on a peer channel,
  -- ending the server only if io
  rsE : ∀ {σ s W X} {e : Net_Api Payload X} {a : X} → SPos σ s → RC s ─[ ev (evl (evLabel X e a)) ]─► W
      → Σ[ s′ ∈ LQ.Tree ] Σ[ σ′ ∈ LQ.SS l × Bool ]
          (W ≡ RC s′ × SPos σ′ s′ × owner e a ≡ false × isPeer e ≡ true × (isES (proj₁ σ′) ≡ true → ioSet (X , e)))
  rsE {s = s} ps st with RP.ren-ev-inv {inv = RnP.ι-vis-inv} {P = s} st
  ... | inj₂ (_ , () , _)
  ... | inj₁ (at , a′ , bt , b , s₁ , sst , eqi , refl , refl) with sE₀ ps sst
  ...   | σ′ , ps′ , own , fn =
          s₁ , σ′ , refl , ps′
        , visImg (λ e x → owner e x ≡ false) bt b at a′ eqi own
        , visImg (λ e _ → isPeer e ≡ true) bt b at a′ eqi (peerι (proj₂ at))
        , λ h → visImg (λ {A} e _ → ioSet (A , e)) bt b at a′ eqi (fn h)

  -- a τ of the renamed server: a loop-back
  rsτ : ∀ {σ s W} → SPos σ s → RC s ─[ τ ]─► W
      → Σ[ s′ ∈ LQ.Tree ] Σ[ σ′ ∈ LQ.SS l × Bool ] (W ≡ RC s′ × SPos σ′ s′ × isES (proj₁ σ′) ≡ false)
  rsτ {s = s} ps st with RP.ren-τ-inv {inv = RnP.ι-vis-inv} {P = s} st
  ... | s₁ , sst , refl with sτ₀ ps sst
  ...   | σ′ , ps′ , ne = s₁ , σ′ , refl , ps′ , ne

  -- the renamed server returns only at its end
  rsR : ∀ {σ s r} → SPos σ s → PTree.force (RC s) ≡ ret r → isES (proj₁ σ) ≡ true
  rsR {s = s} ps eq = sR₀ ps (RP.force-ren-ret-inv {inv = RnP.ι-vis-inv} {P = s} eq)

  -- the renamed server does not offer a client event
  nS : ∀ {σ s X} {e : Net_Api Payload X} {a : X} → SPos σ s → owner e a ≡ true
     → viewV (PTree.force (RC s)) (X , e) a ≡ nothing
  nS {s = s} {X} {e} {a} ps o with viewV (PTree.force (RC s)) (X , e) a in eq
  ... | nothing = refl
  ... | just _ with rsE ps (viewV-ev {P = RC s} refl eq)
  ...   | _ , _ , _ , _ , o′ , _ = ⊥-elim (t≢f (trans (sym o) o′))

  -- the renamed client does not offer a server event
  nC : ∀ {σ c X} {e : Net_Api Payload X} {a : X} → LQ.CPos l σ c → owner e a ≡ false
     → viewV (PTree.force (RC c)) (X , e) a ≡ nothing
  nC {c = c} {X} {e} {a} pc o with viewV (PTree.force (RC c)) (X , e) a in eq
  ... | nothing = refl
  ... | just _ with rcE pc (viewV-ev {P = RC c} refl eq)
  ...   | _ , _ , _ , _ , o′ , _ = ⊥-elim (t≢f (trans (sym o′) o))

  ------------------------------------------------------------------------
  -- §4  The peer pair and the system invariant
  ------------------------------------------------------------------------

  -- the peer pair: the renamed client and server, each at a known phase
  data QSt : Proc → Set₁ where
    qst : ∀ {c s σc σs} → LQ.CPos l σc c → SPos σs s → QSt (Par⊤ ∅ES (RC c) (RC s))

  -- both peers are at their end
  bothEnd : ∀ {q} → QSt q → Bool
  bothEnd (qst {σc = σc} {σs = σs} _ _) = isEC (proj₁ σc) ∧ isES (proj₁ σs)

  -- a τ of the pair: a loop-back of one peer, so the pair is not at its end
  qτ : ∀ {q q′} → QSt q → q ─[ τ ]─► q′ → Σ[ Q′ ∈ QSt q′ ] (bothEnd Q′ ≡ false)
  qτ (qst {c = c} {s = s} pc ps) st with Par-τ-elim ∅ES (λ _ _ → tt) (RC c) (RC s) st
  ... | τL _ cst refl with rcτ pc cst
  ...   | _ , _ , refl , pc′ , ne = qst pc′ ps , ∧-fl ne
  qτ (qst {c = c} {s = s} pc ps) st | τR _ sst refl with rsτ ps sst
  ...   | _ , _ , refl , ps′ , ne = qst pc ps′ , ∧-fr ne

  -- a visible step of the pair: one peer's own event (never both: the owners differ), on a
  -- peer channel; a non-io step leaves the pair not at its end
  qE : ∀ {q q′ X} {e : Net_Api Payload X} {a : X} → QSt q → q ─[ ev (evl (evLabel X e a)) ]─► q′
     → Σ[ Q′ ∈ QSt q′ ] (isPeer e ≡ true × (¬ ioSet (X , e) → bothEnd Q′ ≡ false))
  qE (qst {c = c} {s = s} pc ps) st with Par-ev-elim ∅ES (λ _ _ → tt) (RC c) (RC s) st
  ... | evSync () _ _
  ... | evL _ cst with rcE pc cst
  ...   | _ , _ , refl , pc′ , _ , per , fn = qst pc′ ps , per , λ nio → ∧-fl (bool-false fn nio)
  qE (qst {c = c} {s = s} pc ps) st | evR _ sst with rsE ps sst
  ...   | _ , _ , refl , ps′ , _ , per , fn = qst pc ps′ , per , λ nio → ∧-fr (bool-false fn nio)
  qE (qst {c = c} {s = s} pc ps) st | evBoth _ cst sst with rcE pc cst | rsE ps sst
  ...   | _ , _ , _ , _ , o₁ , _ | _ , _ , _ , _ , o₂ , _ = ⊥-elim (t≢f (trans (sym o₁) o₂))

  -- the pair returns only when both peers are at their end
  qR : ∀ {q r} (Q : QSt q) → PTree.force q ≡ ret r → bothEnd Q ≡ true
  qR (qst {c = c} {s = s} pc ps) eq with Par-force-ret-inv ∅ES (λ _ _ → tt) {P = RC c} {Q = RC s} eq
  ... | _ , _ , fc , fs , _ with rcR pc fc | rsR ps fs
  ...   | ec | es rewrite ec | es = refl

  -- the pair does not offer `break l`
  nQb : ∀ {q} → QSt q → viewV (PTree.force q) (U.⊤ , break l) U.tt ≡ nothing
  nQb {q} Q with viewV (PTree.force q) (U.⊤ , break l) U.tt in eq
  ... | nothing = refl
  ... | just _ with qE Q (viewV-ev {P = q} refl eq)
  ...   | _ , () , _

  -- both peers at their end: the state is finished
  endsDone : ∀ {m q} (Q : QSt q) → bothEnd Q ≡ true → PeersDone (Par⊤ ioES m q)
  endsDone {m} (qst {c = c} {s = s} {σc = σc} pc ps) h with ∧-tt h
  ... | ec , es = m , RC c , RC s , refl
                , RP.force-ren-ret {inv = RnP.ι-vis-inv} {P = c} (LQ.cIntroR l pc (ecFin σc ec))
                , RP.force-ren-ret {inv = RnP.ι-vis-inv} {P = s} (sRetE ps es)

  -- a state BEFORE any break: a live medium against the peer pair
  data Live : Proc → Set₁ where
    live : ∀ {m q} → LiveM m → QSt q → Live (Par⊤ ioES m q)

  -- a state AFTER a break: the medium has returned (it is `Skip`)
  data Broken : Proc → Set₁ where
    broken : ∀ {m q} → PTree.force m ≡ ret tt → QSt q → Broken (Par⊤ ioES m q)

  -- the pair of a broken state is at its end
  bEnd : ∀ {W} → Broken W → Bool
  bEnd (broken _ Q) = bothEnd Q

  -- the initial state is live (cell, client and server at their start)
  inv₀ : Live netPair
  inv₀ = live (cellA , refl , mok₀) (qst LQ.cpI spI)

  -- a τ of a live state stays live
  liveτ : ∀ {W W′} → Live W → W ─[ τ ]─► W′ → Live W′
  liveτ (live {m} {q} lm Q) st with Par-τ-elim ioES (λ _ _ → tt) m q st
  ... | τL _ mst refl = live (mτ lm mst) Q
  ... | τR _ qs  refl = live lm (proj₁ (qτ Q qs))

  -- a visible step of a live state: live again, or it was `break l` and the medium returned
  liveE : ∀ {m q W′ x} → LiveM m → QSt q → Par⊤ ioES m q ─[ ev (evl x) ]─► W′
        → Live W′ ⊎ (x ≡ brkEv × Σ[ m′ ∈ Proc ] (PTree.force m′ ≡ ret tt × W′ ≡ Par⊤ ioES m′ q))
  liveE {m} {q} lm Q st with Par-ev-elim ioES (λ _ _ → tt) m q st
  ... | evSync io mst qs with mE lm mst
  ...   | inj₁ (lm′ , _)  = inj₁ (live lm′ (proj₁ (qE Q qs)))
  ...   | inj₂ (refl , _) = ⊥-elim io
  liveE {m} {q} lm Q st | evL _ mst with mE lm mst
  ...   | inj₁ (lm′ , _)  = inj₁ (live lm′ Q)
  ...   | inj₂ (b , refl) = inj₂ (b , Skip , refl , refl)
  liveE {m} {q} lm Q st | evR _ qs = inj₁ (live lm (proj₁ (qE Q qs)))
  liveE {m} {q} lm Q st | evBoth nio mst qs with mE lm mst | qE Q qs
  ...   | inj₁ (_ , w) | _ , per , _ = ⊥-elim (nio (wp-io _ w per))
  ...   | inj₂ (b , _) | _ , per , _ = ⊥-elim (brkNotPeer b per)

  -- `break l` from a live state: the medium returns, the pair is untouched
  liveBrk : ∀ {m q W′} → LiveM m → QSt q → Par⊤ ioES m q ─[ ev (evl brkEv) ]─► W′
          → Σ[ m′ ∈ Proc ] (PTree.force m′ ≡ ret tt × W′ ≡ Par⊤ ioES m′ q)
  liveBrk {m} {q} lm Q st with Par-ev-elim ioES (λ _ _ → tt) m q st
  ... | evSync () _ _
  ... | evL _ mst with mE lm mst
  ...   | inj₁ (_ , ())
  ...   | inj₂ (_ , refl) = Skip , refl , refl
  liveBrk {m} {q} lm Q st | evR _ qs with qE Q qs
  ...   | _ , () , _
  liveBrk {m} {q} lm Q st | evBoth _ _ qs with qE Q qs
  ...   | _ , () , _

  -- a live state never terminates (the cell never returns)
  liveNo√ : ∀ {W W′ r} → Live W → ¬ (W ─[ ev (√ r) ]─► W′)
  liveNo√ (live {q = q} (x , refl , _) Q) st with Par-ev-elim ioES (λ _ _ → tt) (x △ brk) q st
  ... | ev√ fm _ = △noRet x fm

  -- a τ of a broken state: a peer loop-back
  brkτ : ∀ {W W′} → (B : Broken W) → W ─[ τ ]─► W′ → Σ[ B′ ∈ Broken W′ ] (bEnd B′ ≡ false)
  brkτ (broken {m} {q} fm Q) st with Par-τ-elim ioES (λ _ _ → tt) m q st
  ... | τL _ mst _ = ⊥-elim (ret-no-τ fm mst)
  ... | τR _ qs refl with qτ Q qs
  ...   | Q′ , ne = broken fm Q′ , ne

  -- a visible step of a broken state: a NON-io peer step (the medium is gone)
  brkE : ∀ {W W′ x} → (B : Broken W) → W ─[ ev (evl x) ]─► W′
       → NoIo x × Σ[ B′ ∈ Broken W′ ] (bEnd B′ ≡ false)
  brkE (broken {m} {q} fm Q) st with Par-ev-elim ioES (λ _ _ → tt) m q st
  ... | evSync _ mst _  = ⊥-elim (retNoEv fm mst)
  ... | evL _ mst       = ⊥-elim (retNoEv fm mst)
  ... | evBoth _ mst _  = ⊥-elim (retNoEv fm mst)
  ... | evR nio qs with qE Q qs
  ...   | Q′ , _ , ne = nio , broken fm Q′ , ne nio

  -- a broken state terminates only with the pair at its end
  brk√ : ∀ {W W′ r} → (B : Broken W) → W ─[ ev (√ r) ]─► W′ → bEnd B ≡ true
  brk√ (broken {m} {q} fm Q) st with Par-ev-elim ioES (λ _ _ → tt) m q st
  ... | ev√ _ fq = qR Q fq

  -- every run from a broken state is io-free and stays broken (and leaves the pair not at
  -- its end if it was not)
  bRun : ∀ {W s W′} → (B : Broken W) → W ⟹∖√⟨ s ⟩ W′
       → All NoIo s × Σ[ B′ ∈ Broken W′ ] (bEnd B ≡ false → bEnd B′ ≡ false)
  bRun B ∖√-refl = [] , B , λ ne → ne
  bRun B (∖√-τ st r) with brkτ B st
  ... | B₁ , ne₁ with bRun B₁ r
  ...   | ok , B′ , mono = ok , B′ , λ _ → mono ne₁
  bRun B (∖√-ev st r) with brkE B st
  ... | nio , B₁ , ne₁ with bRun B₁ r
  ...   | ok , B′ , mono = nio ∷ ok , B′ , λ _ → mono ne₁

  -- every run from a live state stays live, or has passed a break into a broken state
  lRun : ∀ {W s W′} → Live W → W ⟹∖√⟨ s ⟩ W′ → Live W′ ⊎ Broken W′
  lRun L ∖√-refl = inj₁ L
  lRun L (∖√-τ st r) = lRun (liveτ L st) r
  lRun (live lm Q) (∖√-ev st r) with liveE lm Q st
  ... | inj₁ L′ = lRun L′ r
  ... | inj₂ (_ , _ , fm , refl) = inj₂ (proj₁ (proj₂ (bRun (broken fm Q) r)))

  -- every run WITHOUT a break from a live state stays live
  lRun₀ : ∀ {W s W′} → Live W → W ⟹∖√⟨ s ⟩ W′ → ¬ Any (_≡ brkEv) s → Live W′
  lRun₀ L ∖√-refl _ = L
  lRun₀ L (∖√-τ st r) nb = lRun₀ (liveτ L st) r nb
  lRun₀ (live lm Q) (∖√-ev st r) nb with liveE lm Q st
  ... | inj₁ L′       = lRun₀ L′ r (λ a → nb (there a))
  ... | inj₂ (eq , _) = ⊥-elim (nb (here eq))

  -- `break l` from any reachable state leads into a broken state
  brkInto : ∀ {W W′} → Live W ⊎ Broken W → W ─[ ev (evl brkEv) ]─► W′ → Broken W′
  brkInto (inj₁ (live lm Q)) b with liveBrk lm Q b
  ... | _ , fm , refl = broken fm Q
  brkInto (inj₂ B) b = proj₁ (proj₂ (brkE B b))

  ------------------------------------------------------------------------
  -- §5  The theorems (i)–(ii)
  ------------------------------------------------------------------------

  -- (i) NO DELIVERY AFTER A BREAK.  Whatever happened before, once `break l` has fired no
  -- io event — `input` or `output`, on ANY link and for ANY mini-protocol id — occurs again:
  -- the medium has returned and `Par` refuses every `ioES` event against it, so what is left
  -- are the peers' api / done events.
  noIoAfterBreak : ∀ {s₁ s₂ W₁ W₂ W₃} → netPair ⟹∖√⟨ s₁ ⟩ W₁ → W₁ ─[ ev (evl brkEv) ]─► W₂
                 → W₂ ⟹∖√⟨ s₂ ⟩ W₃ → All NoIo s₂
  noIoAfterBreak r₁ b r₂ = proj₁ (bRun (brkInto (lRun inv₀ r₁) b) r₂)

  -- (i), trace form: in every √-free trace of the pair that contains `break l`, the part
  -- after (any occurrence of) it has no io event
  noIoAfterBreak-tr : ∀ (s₁ : List Event) {s₂ W} → netPair ⟹∖√⟨ s₁ ++ brkEv ∷ s₂ ⟩ W → All NoIo s₂
  noIoAfterBreak-tr s₁ r with splitRun s₁ r
  ... | _ , _ , r₁ , b , r₂ = noIoAfterBreak r₁ b r₂

  -- a broken state whose pair is not at its end never terminates, whatever happens next
  finish : ∀ {W s W′ W″ r} → (B : Broken W) → bEnd B ≡ false → W ⟹∖√⟨ s ⟩ W′ → ¬ (W′ ─[ ev (√ r) ]─► W″)
  finish B ne r fn with bRun B r
  ... | _ , B′ , mono = t≢f (trans (sym (brk√ B′ fn)) (mono ne))

  -- (ii) AN EARLY BREAK FORFEITS GRACEFUL SHUTDOWN.  If `break l` fires in a reachable state
  -- that is NOT finished (no decomposition with both peers returned — e.g. anywhere before the
  -- client has received MsgDone), then √ is unreachable from there: the medium is gone, a
  -- peer that has not returned can only return by an io step (the client by receiving MsgDone,
  -- the server by sending it), and no io step can happen any more (i).  The pair is left with
  -- only api / done events (informally a handful — a client delivery and command, a server
  -- command or its done — and then stuck; that bound is not proved here).
  earlyBreak-no√ : ∀ {s₁ s₂ W₁ W₂ W₃ W₄ r} → netPair ⟹∖√⟨ s₁ ⟩ W₁ → ¬ PeersDone W₁
                 → W₁ ─[ ev (evl brkEv) ]─► W₂ → W₂ ⟹∖√⟨ s₂ ⟩ W₃ → ¬ (W₃ ─[ ev (√ r) ]─► W₄)
  earlyBreak-no√ r₁ nd b r₂ fn with lRun inv₀ r₁
  ... | inj₁ (live lm Q) with liveBrk lm Q b
  ...   | _ , fm , refl = finish (broken fm Q) (bool-false (endsDone Q) nd) r₂ fn
  earlyBreak-no√ r₁ nd b r₂ fn | inj₂ B with brkE B b
  ...   | _ , B₂ , ne = finish B₂ ne r₂ fn

  ------------------------------------------------------------------------
  -- §6  (iii) Where √ can come from
  ------------------------------------------------------------------------

  -- (iii-a) NO √ WITHOUT A BREAK.  The cell is a `loop0` and never returns (`nr-Copy`), the
  -- interrupt `cell △ brk` is never a `ret` node while the cell is live, and `Par` returns only
  -- when both operands do: every √ of the networked pair has `break l` in its trace.  In
  -- particular a complete Quit / Done handshake WITHOUT a break ends in a stuck state (both
  -- peers returned, the cell still offering `input`), not in √.
  no√WithoutBreak : ∀ {s W W′ r} → netPair ⟹∖√⟨ s ⟩ W → ¬ Any (_≡ brkEv) s → ¬ (W ─[ ev (√ r) ]─► W′)
  no√WithoutBreak r nb fn = liveNo√ (lRun₀ inv₀ r nb) fn

  ---------------------------------------------------------------- intro lemmas for (iii-b)

  -- a source step of a peer, renamed
  ren : ∀ {c c′ X} {e : LNPEv X} {a : X} → c L1.─[ L1.ev (L1.evl (L1.evLabel X e a)) ]─► c′
      → RC c ─[ ev (evl (evLabel X (ιLNP e) a)) ]─► RC c′
  ren {X = X} {e} {a} st =
    RP.ren-ev-fwd {inv = RnP.ι-vis-inv} {at = X , e} {a = a} {bt = X , ιLNP e} {b = a} st (RP.ι-vis-inv-fwd e a)

  -- the system's state: a medium and the two renamed peers
  Sys : Proc → LQ.Tree → LQ.Tree → Proc
  Sys m c s = Par⊤ ioES m (Par⊤ ∅ES (RC c) (RC s))

  -- a client api step (no medium, no server): the server and the live medium do not offer it
  sysApiC : ∀ {x c c′ s σs X} {e : LNPEv X} {a : X} → MedOK x → SPos σs s
          → c L1.─[ L1.ev (L1.evl (L1.evLabel X e a)) ]─► c′
          → ¬ ioSet (X , ιLNP e) → owner (ιLNP e) a ≡ true → isWire (ιLNP e) ≡ false
          → Sys (x △ brk) c s ─[ ev (evl (evLabel X (ιLNP e) a)) ]─► Sys (x △ brk) c′ s
  sysApiC {x} {c} {c′} {s} {e = e} mok ps cst nio o nw =
    Par-soloR ioES (λ _ _ → tt) (x △ brk) (Par⊤ ∅ES (RC c) (RC s)) nio
      (Par-soloL ∅ES (λ _ _ → tt) (RC c) (RC s) (λ ()) (ren cst) (nS ps o)) (nMx mok nw (peerι e))

  -- a server api / done step (no medium, no client): the client and the live medium do not offer it
  sysApiS : ∀ {x c s s′ σc X} {e : LNPEv X} {a : X} → MedOK x → LQ.CPos l σc c
          → s L1.─[ L1.ev (L1.evl (L1.evLabel X e a)) ]─► s′
          → ¬ ioSet (X , ιLNP e) → owner (ιLNP e) a ≡ false → isWire (ιLNP e) ≡ false
          → Sys (x △ brk) c s ─[ ev (evl (evLabel X (ιLNP e) a)) ]─► Sys (x △ brk) c s′
  sysApiS {x} {c} {s} {s′} {e = e} mok pc sst nio o nw =
    Par-soloR ioES (λ _ _ → tt) (x △ brk) (Par⊤ ∅ES (RC c) (RC s)) nio
      (Par-soloR ∅ES (λ _ _ → tt) (RC c) (RC s) (λ ()) (ren sst) (nC pc o)) (nMx mok nw (peerι e))

  -- an io step of the client, synchronised with the medium (the server does not offer it)
  sysSyncC : ∀ {m m′ : Proc} {c c′ s σs X} {e : LNPEv X} {a : X} → SPos σs s
           → m ─[ ev (evl (evLabel X (ιLNP e) a)) ]─► m′ → c L1.─[ L1.ev (L1.evl (L1.evLabel X e a)) ]─► c′
           → ioSet (X , ιLNP e) → owner (ιLNP e) a ≡ true
           → Sys m c s ─[ ev (evl (evLabel X (ιLNP e) a)) ]─► Sys m′ c′ s
  sysSyncC {m} {m′} {c} {c′} {s} ps mst cst io o =
    Par-sync ioES (λ _ _ → tt) m (Par⊤ ∅ES (RC c) (RC s)) io mst
      (Par-soloL ∅ES (λ _ _ → tt) (RC c) (RC s) (λ ()) (ren cst) (nS ps o))

  -- an io step of the server, synchronised with the medium (the client does not offer it)
  sysSyncS : ∀ {m m′ : Proc} {c s s′ σc X} {e : LNPEv X} {a : X} → LQ.CPos l σc c
           → m ─[ ev (evl (evLabel X (ιLNP e) a)) ]─► m′ → s L1.─[ L1.ev (L1.evl (L1.evLabel X e a)) ]─► s′
           → ioSet (X , ιLNP e) → owner (ιLNP e) a ≡ false
           → Sys m c s ─[ ev (evl (evLabel X (ιLNP e) a)) ]─► Sys m′ c s′
  sysSyncS {m} {m′} {c} {s} {s′} pc mst sst io o =
    Par-sync ioES (λ _ _ → tt) m (Par⊤ ∅ES (RC c) (RC s)) io mst
      (Par-soloR ∅ES (λ _ _ → tt) (RC c) (RC s) (λ ()) (ren sst) (nC pc o))

  -- a client τ
  sysτC : ∀ {m c c′ s} → c L1.─[ L1.τ ]─► c′ → Sys m c s ─[ τ ]─► Sys m c′ s
  sysτC {m} {c} {c′} {s} cst =
    Par-τ-R ioES (λ _ _ → tt) m (Par⊤ ∅ES (RC c) (RC s))
      (Par-τ-L ∅ES (λ _ _ → tt) (RC c) (RC s) (RP.ren-τ-fwd {inv = RnP.ι-vis-inv} cst))

  -- a server τ
  sysτS : ∀ {m c s s′} → s L1.─[ L1.τ ]─► s′ → Sys m c s ─[ τ ]─► Sys m c s′
  sysτS {m} {c} {s} {s′} sst =
    Par-τ-R ioES (λ _ _ → tt) m (Par⊤ ∅ES (RC c) (RC s))
      (Par-τ-R ∅ES (λ _ _ → tt) (RC c) (RC s) (RP.ren-τ-fwd {inv = RnP.ι-vis-inv} sst))

  -- a medium τ
  sysτM : ∀ {m m′ : Proc} {c s} → m ─[ τ ]─► m′ → Sys m c s ─[ τ ]─► Sys m′ c s
  sysτM {m} {m′} {c} {s} mst = Par-τ-L ioES (λ _ _ → tt) m (Par⊤ ∅ES (RC c) (RC s)) mst

  -- the medium's break (the peers do not take part)
  sysBrk : ∀ {m m′ q : Proc} → m ─[ ev (evl brkEv) ]─► m′ → viewV (PTree.force q) (U.⊤ , break l) U.tt ≡ nothing
         → Par⊤ ioES m q ─[ ev (evl brkEv) ]─► Par⊤ ioES m′ q
  sysBrk {m} {m′} {q} mst nq = Par-soloL ioES (λ _ _ → tt) m q (λ ()) mst nq

  -- the cell's three states
  cA : Proc
  cA = OM.renameMap (copy-A l lo N2N_LeiosNotify)

  -- (after an input of `x`)
  cB : Payload → Proc
  cB x = OM.renameMap (copy-B l lo N2N_LeiosNotify x)

  -- (after its output, before the loop-back)
  cC : Payload → Proc
  cC x = OM.renameMap (copy-C l lo N2N_LeiosNotify x)

  -- the cell takes `x` in
  cellIn : ∀ x → cA ─[ ev (evl (evLabel Payload (input l lo N2N_LeiosNotify) x)) ]─► cB x
  cellIn x = RN.ren-ev-fwd {inv = OM.ι-vis-inv} {at = Payload , input l lo N2N_LeiosNotify} {a = x}
               {bt = Payload , input l lo N2N_LeiosNotify} {b = x}
               (L0.sVis (proj₂ (proj₂ (probe-A l lo N2N_LeiosNotify))) (probe-A-off l lo N2N_LeiosNotify x)) refl

  -- the cell hands `x` out
  cellOut : ∀ x → cB x ─[ ev (evl (evLabel Payload (output l lo N2N_LeiosNotify) x)) ]─► cC x
  cellOut x = RN.ren-ev-fwd {inv = OM.ι-vis-inv} {at = Payload , output l lo N2N_LeiosNotify} {a = x}
                {bt = Payload , output l lo N2N_LeiosNotify} {b = x}
                (L0.sVis (proj₂ (proj₂ (probe-B l lo N2N_LeiosNotify x))) (probe-B-off l lo N2N_LeiosNotify x)) refl

  -- the cell loops back
  cellτ : ∀ x → cC x ─[ τ ]─► cA
  cellτ x = RN.ren-τ-fwd {inv = OM.ι-vis-inv} (L0.sSil (probe-C l lo N2N_LeiosNotify x))

  -- the medium takes `x` in
  mIn : ∀ x → (cA △ brk) ─[ ev (evl (evLabel Payload (input l lo N2N_LeiosNotify) x)) ]─► (cB x △ brk)
  mIn x = mStepW (cellIn x) refl

  -- the medium hands `x` out
  mOut : ∀ x → (cB x △ brk) ─[ ev (evl (evLabel Payload (output l lo N2N_LeiosNotify) x)) ]─► (cC x △ brk)
  mOut x = mStepW (cellOut x) refl

  -- the medium loops back
  mBack : ∀ x → (cC x △ brk) ─[ τ ]─► (cA △ brk)
  mBack x = △-τ-lift-P (cellτ x)

  -- a client step out of `LQ.cIntroE`
  cS : ∀ {σ σ′ t ω} (pc : LQ.CPos l σ t) (stp : LQ.CStp l σ (LQ.ev′ ω) σ′)
     → t L1.─[ L1.ev (L1.evl (LQ.⌜_⌝ l ω)) ]─► proj₁ (LQ.cIntroE l pc stp)
  cS pc stp = proj₁ (proj₂ (LQ.cIntroE l pc stp))

  -- a server menu offer is a step of the server loop
  sOffL : ∀ st {at a t′} → LQ.vOf (ksL st) at a ≡ just t′
        → OL.iter ksL st L1.─[ L1.ev (L1.evl (L1.evLabel (proj₁ at) (proj₂ at) a)) ]─► OL.iter-bind t′ ksL
  sOffL stIdle eq = LQ.iterE (LQ.pchS eq)
  sOffL stBusy eq = LQ.iterE (LQ.pchS eq)
  sOffL stQuit eq = LQ.iterE (LQ.pchS eq)

  -- the idle server takes RequestNext off the wire
  svRN : ∀ {tm md ln} → OL.iter ksL stIdle
         L1.─[ L1.ev (L1.evl (L1.evLabel _ (receiveLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPRequestNext))) ]─►
         OL.iter-bind (OL.Ret (inj₁ stBusy)) ksL
  svRN {tm} {md} {ln} = sOffL stIdle e
    where
    -- the idle menu accepts RequestNext
    e : LQ.vOf (ksL stIdle) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPRequestNext) ≡ just (OL.Ret (inj₁ stBusy))
    e rewrite LQ.≟-refl l = refl

  -- the idle server takes MsgQuit off the wire
  svQt : ∀ {tm md ln} → OL.iter ksL stIdle
         L1.─[ L1.ev (L1.evl (L1.evLabel _ (receiveLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPQuit))) ]─►
         OL.iter-bind (OL.Ret (inj₁ stQuit)) ksL
  svQt {tm} {md} {ln} = sOffL stIdle e
    where
    -- the idle menu accepts MsgQuit
    e : LQ.vOf (ksL stIdle) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPQuit) ≡ just (OL.Ret (inj₁ stQuit))
    e rewrite LQ.≟-refl l = refl

  -- the busy server is told to cancel
  svCan : OL.iter ksL stBusy L1.─[ L1.ev (L1.evl (L1.evLabel _ (apiLPev l lo lnpSendCanceled) U.tt)) ]─►
          OL.iter-bind (snd l lo FromResponder MsgLNPCanceled stIdle) ksL
  svCan = sOffL stBusy e
    where
    -- the busy menu takes the cancel command
    e : LQ.vOf (ksL stBusy) (_ , apiLPev l lo lnpSendCanceled) U.tt ≡ just (snd l lo FromResponder MsgLNPCanceled stIdle)
    e rewrite LQ.≟-refl l = refl

  -- the quitting server reports its done
  svDn : OL.iter ksL stQuit L1.─[ L1.ev (L1.evl (L1.evLabel _ (doneLNP l lo) U.tt)) ]─►
         OL.iter-bind (OL.Output (sendLNP l lo) (LQ.pay l FromResponder MsgLNPDone) (OL.Ret (inj₂ tt))) ksL
  svDn = sOffL stQuit e
    where
    -- the quit menu offers the peer-local done
    e : LQ.vOf (ksL stQuit) (_ , doneLNP l lo) U.tt
      ≡ just (OL.Output (sendLNP l lo) (LQ.pay l FromResponder MsgLNPDone) (OL.Ret (inj₂ tt)))
    e rewrite LQ.≟-refl l = refl

  -- the server sends its committed reply
  svSnd : ∀ r → OL.iter-bind (snd l lo FromResponder (LQ.repM l r) stIdle) ksL
          L1.─[ L1.ev (L1.evl (L1.evLabel _ (sendLNP l lo) (LQ.pay l FromResponder (LQ.repM l r)))) ]─►
          OL.iter-bind (OL.Ret (inj₁ stIdle)) ksL
  svSnd r = LQ.iterE (LQ.outS (sendLNP l lo) _ _)

  -- the server sends MsgDone and ends
  svDS : OL.iter-bind (OL.Output (sendLNP l lo) (LQ.pay l FromResponder MsgLNPDone) (OL.Ret (inj₂ tt))) ksL
         L1.─[ L1.ev (L1.evl (L1.evLabel _ (sendLNP l lo) (LQ.pay l FromResponder MsgLNPDone))) ]─►
         OL.iter-bind (OL.Ret (inj₂ tt)) ksL
  svDS = LQ.iterE (LQ.outS (sendLNP l lo) _ _)

  -- a payload as the peers build it
  pl : Mode → MessageLeiosNotifyP → Payload
  pl = LQ.pay l

  -- the cell is confined after carrying MsgDone (before its loop-back)
  mokD : MedOK (cC (pl FromResponder MsgLNPDone))
  mokD = mok-step (mok-step mok₀ (cellIn (pl FromResponder MsgLNPDone))) (cellOut (pl FromResponder MsgLNPDone))

  -- the graceful-shutdown trace on link l: RequestNext (commanded, sent, delivered), the
  -- server's cancel (commanded, MsgCanceled sent, delivered), the quit (commanded, MsgQuit sent,
  -- delivered), the server's done, MsgDone (sent, delivered), then the link is closed
  trG : List Event
  trG = evLabel _ (apiLP l lo lnpSendRequestNext) U.tt
      ∷ evLabel _ (input  l lo N2N_LeiosNotify) (pl FromInitiator MsgLNPRequestNext)
      ∷ evLabel _ (output l lo N2N_LeiosNotify) (pl FromInitiator MsgLNPRequestNext)
      ∷ evLabel _ (apiLP l lo lnpSendCanceled) U.tt
      ∷ evLabel _ (input  l lo N2N_LeiosNotify) (pl FromResponder MsgLNPCanceled)
      ∷ evLabel _ (output l lo N2N_LeiosNotify) (pl FromResponder MsgLNPCanceled)
      ∷ evLabel _ (apiLP l lo lnpSendDone) U.tt
      ∷ evLabel _ (input  l lo N2N_LeiosNotify) (pl FromInitiator MsgLNPQuit)
      ∷ evLabel _ (output l lo N2N_LeiosNotify) (pl FromInitiator MsgLNPQuit)
      ∷ evLabel _ (done   l lo N2N_LeiosNotify) U.tt
      ∷ evLabel _ (input  l lo N2N_LeiosNotify) (pl FromResponder MsgLNPDone)
      ∷ evLabel _ (output l lo N2N_LeiosNotify) (pl FromResponder MsgLNPDone)
      ∷ brkEv
      ∷ []

  -- (iii-b) WHERE √ CAN COME FROM.  A concrete run of the networked pair: the full graceful
  -- handshake over the real cell — RequestNext, MsgCanceled, the quit, the server's done,
  -- MsgDone — and then `break l` closes the link; the reached state has returned (√).  With
  -- (iii-a) and (ii): √ needs a break, and a break before the handshake is complete forbids √.
  graceful√ : Σ[ W ∈ Proc ] (netPair ⟹∖√⟨ trG ⟩ W × PTree.force W ≡ ret tt)
  graceful√ = _ , run , fn
    where
    -- the client at its end
    cFin : LQ.Tree
    cFin = OL.iter-bind (OL.Ret (inj₂ tt)) (clientStepP l lo)
    -- the server at its end
    sFin : LQ.Tree
    sFin = OL.iter-bind (OL.Ret (inj₂ tt)) ksL
    -- the run itself, step by step (positions: client `LQ.cp*`, server `sp*`)
    run : netPair ⟹∖√⟨ trG ⟩ Sys Skip
            (OL.iter-bind (OL.Ret (inj₂ tt)) (clientStepP l lo)) (OL.iter-bind (OL.Ret (inj₂ tt)) ksL)
    run =
      ∖√-ev (sysApiC mok₀ spI (cS LQ.cpI (LQ.cRN U.tt)) (λ ()) refl refl)
      (∖√-ev (sysSyncC spI (mIn _) (cS LQ.cpR LQ.cSR) tt refl)
      (∖√-τ (sysτC (L1.sSil refl))
      (∖√-ev (sysSyncS LQ.cpB (mOut _) svRN tt refl)
      (∖√-τ (sysτM (mBack (pl FromInitiator MsgLNPRequestNext)))
      (∖√-τ (sysτS (L1.sSil refl))
      (∖√-ev (sysApiS mok₀ LQ.cpB svCan (λ ()) refl refl)
      (∖√-ev (sysSyncS LQ.cpB (mIn _) (svSnd LQ.rC) tt refl)
      (∖√-τ (sysτS (L1.sSil refl))
      (∖√-ev (sysSyncC spI (mOut _) (cS LQ.cpB LQ.cRC) tt refl)
      (∖√-τ (sysτM (mBack (pl FromResponder MsgLNPCanceled)))
      (∖√-τ (sysτC (L1.sSil refl))
      (∖√-ev (sysApiC mok₀ spI (cS LQ.cpI (LQ.cQi U.tt)) (λ ()) refl refl)
      (∖√-ev (sysSyncC spI (mIn _) (cS LQ.cpS LQ.cSQ) tt refl)
      (∖√-τ (sysτC (L1.sSil refl))
      (∖√-ev (sysSyncS LQ.cpQ (mOut _) svQt tt refl)
      (∖√-τ (sysτM (mBack (pl FromInitiator MsgLNPQuit)))
      (∖√-τ (sysτS (L1.sSil refl))
      (∖√-ev (sysApiS mok₀ LQ.cpQ svDn (λ ()) refl refl)
      (∖√-ev (sysSyncS LQ.cpQ (mIn _) svDS tt refl)
      (∖√-ev (sysSyncC spE (mOut _) (cS LQ.cpQ LQ.cDn) tt refl)
      (∖√-ev (sysBrk (mBrk mokD) (nQb (qst LQ.cpE spE)))
       ∖√-refl)))))))))))))))))))))
    -- the reached state has returned: the medium is `Skip`, both peers have returned
    fn : PTree.force (Sys Skip (OL.iter-bind (OL.Ret (inj₂ tt)) (clientStepP l lo)) (OL.iter-bind (OL.Ret (inj₂ tt)) ksL))
          ≡ ret tt
    fn = fPar-rr ioES (λ _ _ → tt) {P = Skip {0ℓ}} {Q = Par⊤ ∅ES (RC cFin) (RC sFin)} refl
            (fPar-rr ∅ES (λ _ _ → tt) {P = RC cFin} {Q = RC sFin}
              (RP.force-ren-ret {inv = RnP.ι-vis-inv} {P = cFin} refl)
              (RP.force-ren-ret {inv = RnP.ι-vis-inv} {P = sFin} refl))

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano terminable-network example — the terminable copy medium
-- (`CopyT`/`CopySpecT`).
--
-- This is the terminable analogue of `Network.agda`'s `Copy`/`CopySpec`:
--
--   Copy(l,d,id)  = input.l.d.id?x -> output.l.d.id!x -> Copy(l,d,id)
--   CopySpec      = ||| (l,d,id) @ Copy(l,d,id)
--
-- becomes
--
--   CopyT(l,d,id) = input.l.d.id?x -> output.l.d.id!x -> CopyT(l,d,id)
--                [] mdone.l.d.id -> SKIP
--   CopySpecT     = ||| (l,d,id) @ CopyT(l,d,id)
--
-- i.e. each cell can now *terminate* (√) on its own `mdone l d id` event
-- instead of looping forever. `CopyT` is built with `iter` (state = ⊤;
-- `Ret (inj₁ tt)` loops back, `Ret (inj₂ tt)` terminates) rather than
-- `loop0`, so it stays productive without `NON_TERMINATING`.
--
-- This module also derives `allInstances : List (Link × Dir × IDs)` (the
-- flattened `linkConfig` over every link) and `DecEq (Link × Dir × IDs)`,
-- both needed by the later mux-drainer tasks that dispatch `mdone` per
-- configured instance.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.List using (List; map; concatMap; []; _∷_)
open import Data.Vec using (toList; allFin)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees using (PTree; AnyTypes; ContinueType; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base

module CSP.Examples.Cardano_network.Terminable.NetworkT
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open import CSP.Examples.Cardano_network.Net p using (Link)
open import CSP.Examples.Cardano_network.Terminable.NetT p
  using ( NetT; NetT-≟
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; mdone )
open Params p using (numLinks; linkConfig)

import CSP.Operators {E = NetT Data} (NetT-≟ {Data}) as Op
open Op using (⦀⋆; ⦀Fin; pchoice; iter; Ret; Prefix₀; _∥⇘_⇙_; _∖_; chanSet)

------------------------------------------------------------------------
-- A process over the network alphabet, returning the unit on √.
------------------------------------------------------------------------

NetProc : Set₁
NetProc = PTree (NetT Data) (ExtI (NetT Data)) (⊤ {0ℓ})

-- the visible-offer menu type used by (non-terminating) leaves
Menu : Set₁
Menu = (at : AnyTypes (NetT Data)) → ContinueType at (Maybe NetProc)

------------------------------------------------------------------------
-- All configured (link, dir, protocol) instances across every link, and
-- decidable equality on that triple (needed by the later mux drainers).
------------------------------------------------------------------------

-- every link index `Fin numLinks`, as a list
allLinks : List Link
allLinks = toList (allFin numLinks)

-- every configured (link, dir, protocol) instance across all links
allInstances : List (Link × Dir × IDs)
allInstances = concatMap (λ l → map (λ { (d , id) → (l , d , id) }) (linkConfig l)) allLinks

instance
  -- product DecEq for (Dir × IDs), a stepping stone to the triple below
  DecEq-Dir×IDs : DecEq (Dir × IDs)
  DecEq-Dir×IDs = DecEqI.DecEq-×

  -- product DecEq for (Link × Dir × IDs), needed by the mux drainers
  DecEq-Link×Dir×IDs : DecEq (Link × Dir × IDs)
  DecEq-Link×Dir×IDs = DecEqI.DecEq-×

------------------------------------------------------------------------
-- The terminable copy cell.
------------------------------------------------------------------------

-- The iter-state result type shared by the ⊤-state leaves (CopyT/InputT/OutputT):
-- `inj₁ tt` loops, `inj₂ tt` terminates (√).
LeafSt : Set₁
LeafSt = PTree (NetT Data) (ExtI (NetT Data)) (⊤ {0ℓ} ⊎ ⊤ {0ℓ})

-- CopyT's offer menu, lifted to TOP-LEVEL (so the refinement can name the
-- residual `Op.Output (output l d id) x (Ret (inj₁ tt))` and build explicit
-- decode successor terms — mirrors `Network.agda`'s top-level `copyMenu`).
copyTMenu : (l : Link) (d : Dir) (id : IDs)
          → (at : AnyTypes (NetT Data)) → ContinueType at (Maybe LeafSt)
copyTMenu l d id (_ , input l′ d′ id′) x with l′ ≟ l
... | no  _    = nothing
... | yes refl with d′ ≟ d
...   | no  _    = nothing
...   | yes refl with id′ ≟ id
...     | no  _    = nothing
...     | yes refl = just (Op.Output (output l d id) x (Ret (inj₁ tt)))
copyTMenu l d id (_ , mdone l′ d′ id′) _ with l′ ≟ l
... | no  _    = nothing
... | yes refl with d′ ≟ d
...   | no  _    = nothing
...   | yes refl with id′ ≟ id
...     | no  _    = nothing
...     | yes refl = just (Ret (inj₂ tt))
copyTMenu l d id _ _ = nothing

-- terminable copy cell: forward input→output then loop, OR mdone → terminate (√)
CopyT : (l : Link) (d : Dir) (id : IDs) → NetProc
CopyT l d id = iter (λ _ → pchoice (copyTMenu l d id)) tt

-- the copy cells for one link's configured (d, id) instances (unconfigured absent)
linkCopyT : Link → NetProc
linkCopyT l = ⦀⋆ (map (λ { (d , id) → CopyT l d id }) (linkConfig l))

-- the terminable copy medium: every link's bundle, interleaved
CopySpecT : NetProc
CopySpecT = ⦀Fin numLinks linkCopyT

------------------------------------------------------------------------
-- Active-instance-set structural helpers.
--
-- The terminable mux drainers carry the still-live instance set `A` as
-- `iter` state; on `mdone.l.d.id` they drop that instance from `A` (the
-- CSPm `diff(A,{id})`) and √ once `A` is empty.  `mem`/`rm` are the total
-- boolean membership / deletion over `List (Link × Dir × IDs)`, both
-- driven by the Task-5 `DecEq (Link × Dir × IDs)` via `⌊ _≟_ ⌋`.
------------------------------------------------------------------------

-- boolean membership of an instance in the active set
mem : (Link × Dir × IDs) → List (Link × Dir × IDs) → Bool
mem _ []       = false
mem x (y ∷ ys) = ⌊ x ≟ y ⌋ ∨ mem x ys

-- delete every occurrence of an instance from the active set
rm : (Link × Dir × IDs) → List (Link × Dir × IDs) → List (Link × Dir × IDs)
rm _ []       = []
rm x (y ∷ ys) = if ⌊ x ≟ y ⌋ then rm x ys else y ∷ rm x ys

------------------------------------------------------------------------
-- Terminable Tx/Rx leaves.
--
-- `InputT`/`OutputT` are the terminable analogues of `Network.agda`'s
-- `Input`/`Output`: the same forward cycle (tail `Ret (inj₁ tt)` instead
-- of `loop0`'s implicit restart) PLUS an `mdone.l.d.id → Ret (inj₂ tt)`
-- branch that ends the leaf with √.  Built with `iter` (state = ⊤), so
-- productive without `NON_TERMINATING`.
------------------------------------------------------------------------

-- InputT's offer menu, lifted to top-level.
inputTV : (l : Link) (d : Dir) (id : IDs)
        → (at : AnyTypes (NetT Data)) → ContinueType at (Maybe LeafSt)
inputTV l d id (_ , input l′ d′ id′) x with l′ ≟ l
... | no  _    = nothing
... | yes refl with d′ ≟ d
...   | no  _    = nothing
...   | yes refl with id′ ≟ id
...     | no  _    = nothing
...     | yes refl = just (Op.Output (sndmsg l d id) x (rcvack l d id ⟶₀ Ret (inj₁ tt)))
inputTV l d id (_ , mdone l′ d′ id′) _ with l′ ≟ l
... | no  _    = nothing
... | yes refl with d′ ≟ d
...   | no  _    = nothing
...   | yes refl with id′ ≟ id
...     | no  _    = nothing
...     | yes refl = just (Ret (inj₂ tt))
inputTV l d id _ _ = nothing

-- InputT(l,d,id): input?x → sndmsg!x → rcvack → loop, OR mdone → √.
InputT : (l : Link) (d : Dir) (id : IDs) → NetProc
InputT l d id = iter (λ _ → pchoice (inputTV l d id)) tt

-- OutputT's offer menu, lifted to top-level.
outputTV : (l : Link) (d : Dir) (id : IDs)
         → (at : AnyTypes (NetT Data)) → ContinueType at (Maybe LeafSt)
outputTV l d id (_ , rcvmsg l′ d′ id′) x with l′ ≟ l
... | no  _    = nothing
... | yes refl with d′ ≟ d
...   | no  _    = nothing
...   | yes refl with id′ ≟ id
...     | no  _    = nothing
...     | yes refl = just (Op.Output (output l d id) x (sndack l d id ⟶₀ Ret (inj₁ tt)))
outputTV l d id (_ , mdone l′ d′ id′) _ with l′ ≟ l
... | no  _    = nothing
... | yes refl with d′ ≟ d
...   | no  _    = nothing
...   | yes refl with id′ ≟ id
...     | no  _    = nothing
...     | yes refl = just (Ret (inj₂ tt))
outputTV l d id _ _ = nothing

-- OutputT(l,d,id): rcvmsg?x → output!x → sndack → loop, OR mdone → √.
OutputT : (l : Link) (d : Dir) (id : IDs) → NetProc
OutputT l d id = iter (λ _ → pchoice (outputTV l d id)) tt

------------------------------------------------------------------------
-- Config-driven replicated interleavings of the terminable leaves
-- (mirrors `Network.agda`'s `Inputs`/`Outputs`, one live cell per
-- configured `(d, id)` on each link).
------------------------------------------------------------------------

-- Inputs = ||| l @ (||| (d,id) ∈ linkConfig(l) @ InputT(l,d,id))
InputsT : NetProc
InputsT = ⦀Fin numLinks (λ l → ⦀⋆ (map (λ { (d , id) → InputT l d id }) (linkConfig l)))

-- Outputs = ||| l @ (||| (d,id) ∈ linkConfig(l) @ OutputT(l,d,id))
OutputsT : NetProc
OutputsT = ⦀Fin numLinks (λ l → ⦀⋆ (map (λ { (d , id) → OutputT l d id }) (linkConfig l)))

------------------------------------------------------------------------
-- Active-instance-set-draining mux processes.
--
-- Each drainer carries the still-live instance set `A` as `iter` state.
-- It keeps serving its channel action for any instance still in `A`, and
-- on `mdone.l.d.id` (for an instance in `A`) drops that instance from the
-- set (CSPm `\ A -> …(diff(A,{id}))`).  When `A` is empty it terminates
-- with √ (CSPm `if empty(A) then SKIP`).  Built with `iter`, productive.
------------------------------------------------------------------------

-- the drainer state / result tree type (loop with a new set, or √)
DrainSt : Set₁
DrainSt = PTree (NetT Data) (ExtI (NetT Data)) (List (Link × Dir × IDs) ⊎ (⊤ {0ℓ}))

-- TransmitterT's per-set offer menu, lifted to top-level.
transmitterTV : List (Link × Dir × IDs)
              → (at : AnyTypes (NetT Data)) → ContinueType at (Maybe DrainSt)
transmitterTV B (_ , sndmsg l d id) x =
  if mem (l , d , id) B then just (Op.Output (tx l d id) x (Ret (inj₁ B))) else nothing
transmitterTV B (_ , mdone l d id) _ =
  if mem (l , d , id) B then just (Ret (inj₁ (rm (l , d , id) B))) else nothing
transmitterTV B _ _ = nothing

-- TransmitterT's iter step, lifted to top-level.
transmitterTStep : List (Link × Dir × IDs) → DrainSt
transmitterTStep []      = Ret (inj₂ tt)
transmitterTStep (a ∷ A) = pchoice (transmitterTV (a ∷ A))

-- TransmitterT: sndmsg?x → tx!x for live instances; drain on mdone; √ when empty.
TransmitterT : List (Link × Dir × IDs) → NetProc
TransmitterT = iter transmitterTStep

-- ReceiverT's per-set offer menu, lifted to top-level.
receiverTV : List (Link × Dir × IDs)
           → (at : AnyTypes (NetT Data)) → ContinueType at (Maybe DrainSt)
receiverTV B (_ , tx l d id) x =
  if mem (l , d , id) B then just (Op.Output (rcvmsg l d id) x (Ret (inj₁ B))) else nothing
receiverTV B (_ , mdone l d id) _ =
  if mem (l , d , id) B then just (Ret (inj₁ (rm (l , d , id) B))) else nothing
receiverTV B _ _ = nothing

-- ReceiverT's iter step, lifted to top-level.
receiverTStep : List (Link × Dir × IDs) → DrainSt
receiverTStep []      = Ret (inj₂ tt)
receiverTStep (a ∷ A) = pchoice (receiverTV (a ∷ A))

-- ReceiverT: tx?x → rcvmsg!x for live instances; drain on mdone; √ when empty.
ReceiverT : List (Link × Dir × IDs) → NetProc
ReceiverT = iter receiverTStep

-- SndAckT's per-set offer menu, lifted to top-level.
sndAckTV : List (Link × Dir × IDs)
         → (at : AnyTypes (NetT Data)) → ContinueType at (Maybe DrainSt)
sndAckTV B (_ , sndack l d id) _ =
  if mem (l , d , id) B then just (ack l d id ⟶₀ Ret (inj₁ B)) else nothing
sndAckTV B (_ , mdone l d id) _ =
  if mem (l , d , id) B then just (Ret (inj₁ (rm (l , d , id) B))) else nothing
sndAckTV B _ _ = nothing

-- SndAckT's iter step, lifted to top-level.
sndAckTStep : List (Link × Dir × IDs) → DrainSt
sndAckTStep []      = Ret (inj₂ tt)
sndAckTStep (a ∷ A) = pchoice (sndAckTV (a ∷ A))

-- SndAckT: sndack → ack for live instances (payload ignored); drain on mdone; √ empty.
SndAckT : List (Link × Dir × IDs) → NetProc
SndAckT = iter sndAckTStep

-- RcvAckT's per-set offer menu, lifted to top-level.
rcvAckTV : List (Link × Dir × IDs)
         → (at : AnyTypes (NetT Data)) → ContinueType at (Maybe DrainSt)
rcvAckTV B (_ , ack l d id) _ =
  if mem (l , d , id) B then just (rcvack l d id ⟶₀ Ret (inj₁ B)) else nothing
rcvAckTV B (_ , mdone l d id) _ =
  if mem (l , d , id) B then just (Ret (inj₁ (rm (l , d , id) B))) else nothing
rcvAckTV B _ _ = nothing

-- RcvAckT's iter step, lifted to top-level.
rcvAckTStep : List (Link × Dir × IDs) → DrainSt
rcvAckTStep []      = Ret (inj₂ tt)
rcvAckTStep (a ∷ A) = pchoice (rcvAckTV (a ∷ A))

-- RcvAckT: ack → rcvack for live instances (payload ignored); drain on mdone; √ empty.
RcvAckT : List (Link × Dir × IDs) → NetProc
RcvAckT = iter rcvAckTStep

------------------------------------------------------------------------
-- Channel-level synchronisation / hiding sets.
--
-- The HIDE sets `csSR`/`csRS`/`csTA` are exactly those of `Network.agda`
-- and EXCLUDE `mdone` (redefined locally so `mdone` stays observable
-- through the hides).  The SYNC interfaces additionally carry `mdone`
-- (`…d` variants), plus a `mdone`-only set `csMD` synchronising the leaf
-- √'s with the drainers' set-draining.
------------------------------------------------------------------------

-- {| sndmsg, rcvack |}   (hide set — no mdone)
csSR : AnyTypes (NetT Data) → Set
csSR (_ , sndmsg _ _ _) = ⊤
csSR (_ , rcvack _ _ _) = ⊤
csSR _                  = ⊥

csSR-dec : (at : AnyTypes (NetT Data)) → Dec (csSR at)
csSR-dec (_ , sndmsg _ _ _) = yes tt
csSR-dec (_ , rcvack _ _ _) = yes tt
csSR-dec (_ , input _ _ _)  = no λ ()
csSR-dec (_ , output _ _ _) = no λ ()
csSR-dec (_ , rcvmsg _ _ _) = no λ ()
csSR-dec (_ , tx _ _ _)     = no λ ()
csSR-dec (_ , sndack _ _ _) = no λ ()
csSR-dec (_ , ack _ _ _)    = no λ ()
csSR-dec (_ , mdone _ _ _)  = no λ ()

-- {| rcvmsg, sndack |}   (hide set — no mdone)
csRS : AnyTypes (NetT Data) → Set
csRS (_ , rcvmsg _ _ _) = ⊤
csRS (_ , sndack _ _ _) = ⊤
csRS _                  = ⊥

csRS-dec : (at : AnyTypes (NetT Data)) → Dec (csRS at)
csRS-dec (_ , rcvmsg _ _ _) = yes tt
csRS-dec (_ , sndack _ _ _) = yes tt
csRS-dec (_ , input _ _ _)  = no λ ()
csRS-dec (_ , output _ _ _) = no λ ()
csRS-dec (_ , sndmsg _ _ _) = no λ ()
csRS-dec (_ , tx _ _ _)     = no λ ()
csRS-dec (_ , rcvack _ _ _) = no λ ()
csRS-dec (_ , ack _ _ _)    = no λ ()
csRS-dec (_ , mdone _ _ _)  = no λ ()

-- {| tx, ack |}   (hide set — no mdone)
csTA : AnyTypes (NetT Data) → Set
csTA (_ , tx _ _ _) = ⊤
csTA (_ , ack _ _ _) = ⊤
csTA _              = ⊥

csTA-dec : (at : AnyTypes (NetT Data)) → Dec (csTA at)
csTA-dec (_ , tx _ _ _)     = yes tt
csTA-dec (_ , ack _ _ _)    = yes tt
csTA-dec (_ , input _ _ _)  = no λ ()
csTA-dec (_ , output _ _ _) = no λ ()
csTA-dec (_ , sndmsg _ _ _) = no λ ()
csTA-dec (_ , rcvmsg _ _ _) = no λ ()
csTA-dec (_ , sndack _ _ _) = no λ ()
csTA-dec (_ , rcvack _ _ _) = no λ ()
csTA-dec (_ , mdone _ _ _)  = no λ ()

-- {| sndmsg, rcvack, mdone |}   (Tx-leaf ↔ mux sync interface)
csSRd : AnyTypes (NetT Data) → Set
csSRd (_ , sndmsg _ _ _) = ⊤
csSRd (_ , rcvack _ _ _) = ⊤
csSRd (_ , mdone _ _ _)  = ⊤
csSRd _                  = ⊥

csSRd-dec : (at : AnyTypes (NetT Data)) → Dec (csSRd at)
csSRd-dec (_ , sndmsg _ _ _) = yes tt
csSRd-dec (_ , rcvack _ _ _) = yes tt
csSRd-dec (_ , mdone _ _ _)  = yes tt
csSRd-dec (_ , input _ _ _)  = no λ ()
csSRd-dec (_ , output _ _ _) = no λ ()
csSRd-dec (_ , rcvmsg _ _ _) = no λ ()
csSRd-dec (_ , tx _ _ _)     = no λ ()
csSRd-dec (_ , sndack _ _ _) = no λ ()
csSRd-dec (_ , ack _ _ _)    = no λ ()

-- {| rcvmsg, sndack, mdone |}   (Rx-leaf ↔ mux sync interface)
csRSd : AnyTypes (NetT Data) → Set
csRSd (_ , rcvmsg _ _ _) = ⊤
csRSd (_ , sndack _ _ _) = ⊤
csRSd (_ , mdone _ _ _)  = ⊤
csRSd _                  = ⊥

csRSd-dec : (at : AnyTypes (NetT Data)) → Dec (csRSd at)
csRSd-dec (_ , rcvmsg _ _ _) = yes tt
csRSd-dec (_ , sndack _ _ _) = yes tt
csRSd-dec (_ , mdone _ _ _)  = yes tt
csRSd-dec (_ , input _ _ _)  = no λ ()
csRSd-dec (_ , output _ _ _) = no λ ()
csRSd-dec (_ , sndmsg _ _ _) = no λ ()
csRSd-dec (_ , tx _ _ _)     = no λ ()
csRSd-dec (_ , rcvack _ _ _) = no λ ()
csRSd-dec (_ , ack _ _ _)    = no λ ()

-- {| tx, ack, mdone |}   (Tx-side ↔ Rx-side sync interface)
csTAd : AnyTypes (NetT Data) → Set
csTAd (_ , tx _ _ _) = ⊤
csTAd (_ , ack _ _ _) = ⊤
csTAd (_ , mdone _ _ _) = ⊤
csTAd _              = ⊥

csTAd-dec : (at : AnyTypes (NetT Data)) → Dec (csTAd at)
csTAd-dec (_ , tx _ _ _)     = yes tt
csTAd-dec (_ , ack _ _ _)    = yes tt
csTAd-dec (_ , mdone _ _ _)  = yes tt
csTAd-dec (_ , input _ _ _)  = no λ ()
csTAd-dec (_ , output _ _ _) = no λ ()
csTAd-dec (_ , sndmsg _ _ _) = no λ ()
csTAd-dec (_ , rcvmsg _ _ _) = no λ ()
csTAd-dec (_ , sndack _ _ _) = no λ ()
csTAd-dec (_ , rcvack _ _ _) = no λ ()

-- {| mdone |}   (leaf √ ↔ ack-drainer set-draining sync interface)
csMD : AnyTypes (NetT Data) → Set
csMD (_ , mdone _ _ _) = ⊤
csMD _                 = ⊥

csMD-dec : (at : AnyTypes (NetT Data)) → Dec (csMD at)
csMD-dec (_ , mdone _ _ _)  = yes tt
csMD-dec (_ , input _ _ _)  = no λ ()
csMD-dec (_ , output _ _ _) = no λ ()
csMD-dec (_ , sndmsg _ _ _) = no λ ()
csMD-dec (_ , rcvmsg _ _ _) = no λ ()
csMD-dec (_ , tx _ _ _)     = no λ ()
csMD-dec (_ , sndack _ _ _) = no λ ()
csMD-dec (_ , rcvack _ _ _) = no λ ()
csMD-dec (_ , ack _ _ _)    = no λ ()

------------------------------------------------------------------------
-- The two sides and the whole terminable Network.
--
-- `mdone` is in EVERY sync interface (…d + csMD) so a leaf's √ drives the
-- corresponding mux drainer to drop that instance; it is hidden in NONE
-- of the hides (csSR/csRS/csTA), so `mdone` stays observable at the top.
------------------------------------------------------------------------

-- TxSideT: Inputs synchronised with (Transmitter ‖ RcvAck) on sndmsg/rcvack/mdone,
-- then sndmsg/rcvack hidden (mdone kept).
TxSideT : NetProc
TxSideT = (InputsT ∥⇘ chanSet csSRd csSRd-dec ⇙
            (TransmitterT allInstances ∥⇘ chanSet csMD csMD-dec ⇙ RcvAckT allInstances))
            ∖ chanSet csSR csSR-dec

-- RxSideT: Outputs synchronised with (Receiver ‖ SndAck) on rcvmsg/sndack/mdone,
-- then rcvmsg/sndack hidden (mdone kept).
RxSideT : NetProc
RxSideT = (OutputsT ∥⇘ chanSet csRSd csRSd-dec ⇙
            (ReceiverT allInstances ∥⇘ chanSet csMD csMD-dec ⇙ SndAckT allInstances))
            ∖ chanSet csRS csRS-dec

-- NetworkT: the two sides synchronised on tx/ack/mdone, then tx/ack hidden
-- (mdone kept observable).
NetworkT : NetProc
NetworkT = (TxSideT ∥⇘ chanSet csTAd csTAd-dec ⇙ RxSideT)
             ∖ chanSet csTA csTA-dec

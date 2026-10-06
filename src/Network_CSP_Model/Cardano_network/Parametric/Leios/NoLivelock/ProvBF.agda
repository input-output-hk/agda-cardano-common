{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C (D1-b, shipped route): the BLOCK CHAIN relation
-- and one PEER HOP of it.  `ChS e b` — label `e` carries ranking block `b` on
-- the route forge → store → server thread → BF server → medium → BF
-- client → client thread → store.  The BlockFetch CLIENT reports only
-- blocks it has just received (`bfClient-prov`), at the source alphabet,
-- then carried onto `Net_Api` (`Prov-ren`).  The BF SERVER side is
-- `BFserverA-PA`, renamed across `ιBF`/`ιBF⁻¹` with its exact-inverse proof
-- `ιBF-rinv`.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.ProvBF (p : Params) where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (_≟_)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.BlockFetch p
open import Cardano_network.NetworkPar p using (ιBF)
open Params p using (Block; time₀; length₀)
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as L
import Semantics.LTS {E = BFEv} {I = ExtI BFEv} as B
open import CSP.Laws.DivFree.Prov BFEv-≟
open import CSP.Operators BFEv-≟ using (Output; Ret)
open import CSP.Laws.DivFree.Count BFEv-≟ using (labels)
open import Semantics.Failures {E = BFEv} {I = ExtI BFEv} using (_⟹⟨_⟩_)

------------------------------------------------------------------------
-- the chain (system level, on `Net_Api`)
------------------------------------------------------------------------

-- the block a wire payload carries (a BlockFetch `MsgBlock`), if any
msgBlk : Payload → Maybe Block
msgBlk (_ , _ , _ , blockFetch (MsgBlock b)) = just b
msgBlk _                                     = nothing

-- THE BLOCK CHAIN: the labels that carry a ranking block along its route (on the wire,
-- only the BlockFetch cells: no other protocol's peer ever touches the chain)
ChS : L.Event → Block → Set
ChS (L.evLabel _ (input _ _ N2N_BlockFetch) pl)  y = msgBlk pl ≡ just y
ChS (L.evLabel _ (output _ _ N2N_BlockFetch) pl) y = msgBlk pl ≡ just y
ChS (L.evLabel _ (apiBF _ _ sendBFBlock) b)  y = b ≡ y
ChS (L.evLabel _ (apiBF _ _ recvBFBlock) b)  y = b ≡ y
ChS (L.evLabel _ (store _ _ stPut) b)        y = b ≡ y
ChS (L.evLabel _ (store _ _ stGet) b)        y = b ≡ y
ChS (L.evLabel _ (store _ _ (stGetAt _)) b)  y = b ≡ y
ChS (L.evLabel _ (env _ _ envForge) (_ , b)) y = b ≡ y
ChS _                                        y = ⊥

-- what a PEER relies on: a block delivered to it by the medium, or handed to it by a thread
InP : L.Event → Block → Set
InP (L.evLabel _ (output _ _ N2N_BlockFetch) pl) y = msgBlk pl ≡ just y
InP (L.evLabel _ (apiBF _ _ sendBFBlock) b)  y = b ≡ y
InP _                                        y = ⊥

------------------------------------------------------------------------
-- the BlockFetch client, at its source alphabet
------------------------------------------------------------------------

-- the BlockFetch renaming on labels
renE : B.Event → L.Event
renE (B.evLabel A e a) = L.evLabel A (ιBF e) a

-- the chain and the peer rely, pulled back to `BFEv`
ChB InB : B.Event → Block → Set
ChB e = ChS (renE e)
InB e = InP (renE e)

-- Idle: what a step can be (the api menu; each a single block-free send)
data IdleV (l : Link) (d : Dir) : B.Event → PTree BFEv (ExtI BFEv) (BFState ⊎ Rr) → Set₁ where
  iRange : ∀ r → IdleV l d (B.evLabel _ (apiBFev l d sendBFRequestRange) r)
             (sendBF l d ! (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ⟶ Ret (inj₁ stBusy))
  iDone  : ∀ u → IdleV l d (B.evLabel _ (apiBFev l d sendBFClientDone) u)
             (sendBF l d ! (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ⟶ Ret (inj₁ stDone))

-- the Idle inversion
idleV : ∀ {l d x t′} → clientStep l d stIdle B.─[ B.ev (B.evl x) ]─► t′ → IdleV l d x t′
idleV {l} {d} (B.sVis {at = _ , apiBFev l′ d′ sendBFRequestRange} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (IdleV l d _) (just-injective br) (iRange _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
idleV {l} {d} (B.sVis {at = _ , apiBFev l′ d′ sendBFClientDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (IdleV l d _) (just-injective br) (iDone _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
idleV (B.sVis {at = _ , apiBFev _ _ sendBFStartBatch} refl ())
idleV (B.sVis {at = _ , apiBFev _ _ sendBFNoBlocks} refl ())
idleV (B.sVis {at = _ , apiBFev _ _ sendBFBlock} refl ())
idleV (B.sVis {at = _ , apiBFev _ _ sendBFBatchDone} refl ())
idleV (B.sVis {at = _ , apiBFev _ _ recvBFBlock} refl ())
idleV (B.sVis {at = _ , apiBFev _ _ reqBFRange} refl ())
idleV (B.sVis {at = _ , sendBF _ _} refl ())
idleV (B.sVis {at = _ , receiveBF _ _} refl ())
idleV (B.sVis {at = _ , doneBF _ _} refl ())

-- Busy: what a step can be (StartBatch / NoBlocks received, nothing sent)
data BusyV (l : Link) (d : Dir) : B.Event → PTree BFEv (ExtI BFEv) (BFState ⊎ Rr) → Set₁ where
  bStart : ∀ {t m n} → BusyV l d (B.evLabel _ (receiveBF l d) (t , m , n , blockFetch MsgStartBatch)) (Ret (inj₁ stStreaming))
  bNone  : ∀ {t m n} → BusyV l d (B.evLabel _ (receiveBF l d) (t , m , n , blockFetch MsgNoBlocks)) (Ret (inj₁ stIdle))

-- the Busy inversion
busyV : ∀ {l d x t′} → clientStep l d stBusy B.─[ B.ev (B.evl x) ]─► t′ → BusyV l d x t′
busyV {l} {d} (B.sVis {at = _ , receiveBF l′ d′} {a = _ , _ , _ , blockFetch MsgStartBatch} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (BusyV l d _) (just-injective br) bStart
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
busyV {l} {d} (B.sVis {at = _ , receiveBF l′ d′} {a = _ , _ , _ , blockFetch MsgNoBlocks} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (BusyV l d _) (just-injective br) bNone
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch (MsgRequestRange _)} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch (MsgBlock _)} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch MsgBatchDone} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch MsgClientDone} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , keepAlive _} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , chainSync _} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , txSubmission _} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosNotify _} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosFetch _} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
busyV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
busyV (B.sVis {at = _ , sendBF _ _} refl ())
busyV (B.sVis {at = _ , apiBFev _ _ _} refl ())
busyV (B.sVis {at = _ , doneBF _ _} refl ())

-- Streaming: what a step can be — THE HOP: a received `MsgBlock b` is reported as `recvBFBlock b`
data StrV (l : Link) (d : Dir) : B.Event → PTree BFEv (ExtI BFEv) (BFState ⊎ Rr) → Set₁ where
  sBlock : ∀ {t m n} b → StrV l d (B.evLabel _ (receiveBF l d) (t , m , n , blockFetch (MsgBlock b)))
                           (apiBFev l d recvBFBlock ! b ⟶ Ret (inj₁ stStreaming))
  sDone  : ∀ {t m n} → StrV l d (B.evLabel _ (receiveBF l d) (t , m , n , blockFetch MsgBatchDone)) (Ret (inj₁ stIdle))

-- the Streaming inversion
strV : ∀ {l d x t′} → clientStep l d stStreaming B.─[ B.ev (B.evl x) ]─► t′ → StrV l d x t′
strV {l} {d} (B.sVis {at = _ , receiveBF l′ d′} {a = _ , _ , _ , blockFetch (MsgBlock b)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (StrV l d _) (just-injective br) (sBlock b)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
strV {l} {d} (B.sVis {at = _ , receiveBF l′ d′} {a = _ , _ , _ , blockFetch MsgBatchDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (StrV l d _) (just-injective br) sDone
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch (MsgRequestRange _)} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch MsgStartBatch} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch MsgNoBlocks} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch MsgClientDone} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , keepAlive _} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , chainSync _} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , txSubmission _} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosNotify _} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosFetch _} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
strV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
strV (B.sVis {at = _ , sendBF _ _} refl ())
strV (B.sVis {at = _ , apiBFev _ _ _} refl ())
strV (B.sVis {at = _ , doneBF _ _} refl ())

------------------------------------------------------------------------
-- provenance, read off the views (the part specific to D1-b)
------------------------------------------------------------------------

-- the obligation of a step and the provenance of what follows it
StepP : (Block → Set) → B.Event → PTree BFEv (ExtI BFEv) (BFState ⊎ Rr) → Set₁
StepP K x t′ = (∀ {y} → ChB x y → InB x y ⊎ K y) × ProvT ChB ChB InB (λ y → K y ⊎ ChB x y) t′

-- Idle sends no block
idleP : ∀ {l d K x t′} → IdleV l d x t′ → StepP K x t′
idleP (iRange _) = (λ ()) , ProvT-Output _ _ (λ ()) ProvT-Ret
idleP (iDone _)  = (λ ()) , ProvT-Output _ _ (λ ()) ProvT-Ret

-- Busy only receives
busyP : ∀ {l d K x t′} → BusyV l d x t′ → StepP K x t′
busyP bStart = inj₁ , ProvT-Ret
busyP bNone  = inj₁ , ProvT-Ret

-- Streaming: the reported block is the one just received
strP : ∀ {l d K x t′} → StrV l d x t′ → StepP K x t′
strP (sBlock b) = inj₁ , ProvT-Output _ b (λ { refl → inj₂ (inj₂ refl) }) ProvT-Ret
strP sDone      = inj₁ , ProvT-Ret

-- every round of the client justifies its own block reports
roundP : ∀ {l d} st → ProvT ChB ChB InB (λ _ → ⊥) (clientStep l d st)
roundP stIdle      = ProvT-pchoice (λ st → idleP (idleV st))
roundP stBusy      = ProvT-pchoice (λ st → busyP (busyV st))
roundP stStreaming = ProvT-pchoice (λ st → strP (strV st))
roundP stDone      = ProvT-Ret

-- THE PEER HOP (source alphabet): every block the client reports, it has received before
bfClient-prov : ∀ l d {K s W} → BFclientStClient l d ⟹⟨ s ⟩ W
              → Prov ChB ChB InB K (labels s)
bfClient-prov l d tr = provIter (clientStep l d) (λ st → roundP st) stIdle tr

------------------------------------------------------------------------
-- carried onto `Net_Api` (the label map; the trace correspondence of a
-- `renameMap` run is `CountRename.ren-trace-elim-rel`, Task 2)
------------------------------------------------------------------------

import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) as PL

-- provenance of pulled-back predicates is provenance of the mapped labels
Prov-map : ∀ {O Kp In : L.Event → Block → Set} {K} (ls : List B.Event)
         → Prov (λ e → O (renE e)) (λ e → Kp (renE e)) (λ e → In (renE e)) K ls
         → PL.Prov O Kp In K (map renE ls)
Prov-map []       _       = tt
Prov-map (e ∷ ls) (h , q) = h , Prov-map ls q

-- THE PEER HOP on `Net_Api` labels
bfClient-provA : ∀ l d {K s W} → BFclientStClient l d ⟹⟨ s ⟩ W
               → PL.Prov ChS ChS InP K (map renE (labels s))
bfClient-provA l d tr = Prov-map _ (bfClient-prov l d tr)

------------------------------------------------------------------------
-- the BlockFetch SERVER, at its source alphabet: views, provenance
------------------------------------------------------------------------

open import CSP.Operators BFEv-≟ using (Prefix; Prefix₀)
open import Relation.Binary.PropositionalEquality using (cong)
open import Function using (case_of_)

-- a BlockFetch round tree
RdB : Set₁
RdB = PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)

-- Idle: the receive menu (a range request, reported; ClientDone)
data SIdleV (l : Link) (d : Dir) : B.Event → RdB → Set₁ where
  siRange : ∀ {t m n} r → SIdleV l d (B.evLabel _ (receiveBF l d) (t , m , n , blockFetch (MsgRequestRange r)))
                                     (apiBFev l d reqBFRange ! r ⟶ Ret (inj₁ stBusy))
  siDone  : ∀ {t m n}   → SIdleV l d (B.evLabel _ (receiveBF l d) (t , m , n , blockFetch MsgClientDone))
                                     (doneBF l d ⟶₀ Ret (inj₁ stDone))

-- the server Idle inversion
sIdleV : ∀ {l d x t′} → serverStep l d stIdle B.─[ B.ev (B.evl x) ]─► t′ → SIdleV l d x t′
sIdleV {l} {d} (B.sVis {at = _ , receiveBF l′ d′} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) (siRange r)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV {l} {d} (B.sVis {at = _ , receiveBF l′ d′} {a = _ , _ , _ , blockFetch MsgClientDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) siDone
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch MsgStartBatch} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch MsgNoBlocks} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch (MsgBlock _)} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch MsgBatchDone} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , keepAlive _} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , chainSync _} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , txSubmission _} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosNotify _} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosFetch _} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
sIdleV (B.sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
sIdleV (B.sVis {at = _ , sendBF _ _} refl ())
sIdleV (B.sVis {at = _ , apiBFev _ _ _} refl ())
sIdleV (B.sVis {at = _ , doneBF _ _} refl ())

-- the server's answer `msg`, then on to `st`
bSend : Link → Dir → MessageBlockFetch → BFState → RdB
bSend l d msg st = sendBF l d ! (time₀ , FromResponder , length₀ , blockFetch msg) ⟶ Ret (inj₁ st)

-- Busy: the api menu (StartBatch / NoBlocks), each a single block-free send
data SBusyV (l : Link) (d : Dir) : B.Event → RdB → Set₁ where
  sbStart : ∀ u → SBusyV l d (B.evLabel _ (apiBFev l d sendBFStartBatch) u) (bSend l d MsgStartBatch stStreaming)
  sbNone  : ∀ u → SBusyV l d (B.evLabel _ (apiBFev l d sendBFNoBlocks) u) (bSend l d MsgNoBlocks stIdle)

-- the server Busy inversion
sBusyV : ∀ {l d x t′} → serverStep l d stBusy B.─[ B.ev (B.evl x) ]─► t′ → SBusyV l d x t′
sBusyV {l} {d} (B.sVis {at = _ , apiBFev l′ d′ sendBFStartBatch} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBusyV l d _) (just-injective br) (sbStart _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBusyV {l} {d} (B.sVis {at = _ , apiBFev l′ d′ sendBFNoBlocks} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBusyV l d _) (just-injective br) (sbNone _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBusyV (B.sVis {at = _ , apiBFev _ _ sendBFRequestRange} refl ())
sBusyV (B.sVis {at = _ , apiBFev _ _ sendBFClientDone} refl ())
sBusyV (B.sVis {at = _ , apiBFev _ _ sendBFBlock} refl ())
sBusyV (B.sVis {at = _ , apiBFev _ _ sendBFBatchDone} refl ())
sBusyV (B.sVis {at = _ , apiBFev _ _ recvBFBlock} refl ())
sBusyV (B.sVis {at = _ , apiBFev _ _ reqBFRange} refl ())
sBusyV (B.sVis {at = _ , sendBF _ _} refl ())
sBusyV (B.sVis {at = _ , receiveBF _ _} refl ())
sBusyV (B.sVis {at = _ , doneBF _ _} refl ())

-- Streaming: the api menu (a block / BatchDone), each a single send
data SStrV (l : Link) (d : Dir) : B.Event → RdB → Set₁ where
  ssBlock : ∀ b → SStrV l d (B.evLabel _ (apiBFev l d sendBFBlock) b)
                            (sendBF l d ! (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ⟶ Ret (inj₁ stStreaming))
  ssDone  : ∀ u → SStrV l d (B.evLabel _ (apiBFev l d sendBFBatchDone) u) (bSend l d MsgBatchDone stIdle)

-- the server Streaming inversion
sStrV : ∀ {l d x t′} → serverStep l d stStreaming B.─[ B.ev (B.evl x) ]─► t′ → SStrV l d x t′
sStrV {l} {d} (B.sVis {at = _ , apiBFev l′ d′ sendBFBlock} {a = b} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SStrV l d _) (just-injective br) (ssBlock b)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sStrV {l} {d} (B.sVis {at = _ , apiBFev l′ d′ sendBFBatchDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SStrV l d _) (just-injective br) (ssDone _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sStrV (B.sVis {at = _ , apiBFev _ _ sendBFRequestRange} refl ())
sStrV (B.sVis {at = _ , apiBFev _ _ sendBFClientDone} refl ())
sStrV (B.sVis {at = _ , apiBFev _ _ sendBFStartBatch} refl ())
sStrV (B.sVis {at = _ , apiBFev _ _ sendBFNoBlocks} refl ())
sStrV (B.sVis {at = _ , apiBFev _ _ recvBFBlock} refl ())
sStrV (B.sVis {at = _ , apiBFev _ _ reqBFRange} refl ())
sStrV (B.sVis {at = _ , sendBF _ _} refl ())
sStrV (B.sVis {at = _ , receiveBF _ _} refl ())
sStrV (B.sVis {at = _ , doneBF _ _} refl ())

-- Idle: a request carries no block
sIdleP : ∀ {l d K x t′} → SIdleV l d x t′ → StepP K x t′
sIdleP (siRange _) = inj₁ , ProvT-Output _ _ (λ ()) ProvT-Ret
sIdleP siDone      = inj₁ , ProvT-⟶ _ (λ _ ()) (λ _ → ProvT-Ret)

-- Busy: the batch announcements carry no block
sBusyP : ∀ {l d K x t′} → SBusyV l d x t′ → StepP K x t′
sBusyP (sbStart _) = (λ ()) , ProvT-Output _ _ (λ ()) ProvT-Ret
sBusyP (sbNone _)  = (λ ()) , ProvT-Output _ _ (λ ()) ProvT-Ret

-- Streaming — THE SERVER HOP: the block put on the wire is the one the api handed over
sStrP : ∀ {l d K x t′} → SStrV l d x t′ → StepP K x t′
sStrP (ssBlock b) = inj₁ , ProvT-Output _ _ (λ { refl → inj₂ (inj₂ refl) }) ProvT-Ret
sStrP (ssDone _)  = (λ ()) , ProvT-Output _ _ (λ ()) ProvT-Ret

-- every round of the server justifies its own block sends
sRoundP : ∀ {l d} st → ProvT ChB ChB InB (λ _ → ⊥) (serverStep l d st)
sRoundP stIdle      = ProvT-pchoice (λ st → sIdleP (sIdleV st))
sRoundP stBusy      = ProvT-pchoice (λ st → sBusyP (sBusyV st))
sRoundP stStreaming = ProvT-pchoice (λ st → sStrP (sStrV st))
sRoundP stDone      = ProvT-Ret

-- THE SERVER HOP (source alphabet): every block the server sends, its thread handed it
bfServer-prov : ∀ l d {K s W} → BFserverStClient l d ⟹⟨ s ⟩ W
              → Prov ChB ChB InB K (labels s)
bfServer-prov l d tr = provIter (serverStep l d) (λ st → sRoundP st) stIdle tr

------------------------------------------------------------------------
-- both peers on `Net_Api`, through `renameMap` (`CountRename`)
------------------------------------------------------------------------

open import Cardano_network.NetworkPar p using (ιBF⁻¹; ιBF-linv; BFclientA; BFserverA)

-- ιBF⁻¹ pulls back only ιBF-images
ιBF-rinv : ∀ {A} {e₂ : Net_Api Payload A} {e : BFEv A} → ιBF⁻¹ e₂ ≡ just e → e₂ ≡ ιBF e
ιBF-rinv {e₂ = input  _ _ N2N_BlockFetch} refl = refl
ιBF-rinv {e₂ = output _ _ N2N_BlockFetch} refl = refl
ιBF-rinv {e₂ = apiBF  _ _ _}             refl = refl
ιBF-rinv {e₂ = done   _ _ N2N_BlockFetch} refl = refl
ιBF-rinv {e₂ = input  _ _ N2N_ChainSync} ()
ιBF-rinv {e₂ = input  _ _ N2N_TxSubmission} ()
ιBF-rinv {e₂ = input  _ _ N2N_KeepAlive} ()
ιBF-rinv {e₂ = input  _ _ N2N_LeiosNotify} ()
ιBF-rinv {e₂ = input  _ _ N2N_LeiosFetch} ()
ιBF-rinv {e₂ = output _ _ N2N_ChainSync} ()
ιBF-rinv {e₂ = output _ _ N2N_TxSubmission} ()
ιBF-rinv {e₂ = output _ _ N2N_KeepAlive} ()
ιBF-rinv {e₂ = output _ _ N2N_LeiosNotify} ()
ιBF-rinv {e₂ = output _ _ N2N_LeiosFetch} ()
ιBF-rinv {e₂ = done   _ _ N2N_ChainSync} ()
ιBF-rinv {e₂ = done   _ _ N2N_TxSubmission} ()
ιBF-rinv {e₂ = done   _ _ N2N_KeepAlive} ()
ιBF-rinv {e₂ = done   _ _ N2N_LeiosNotify} ()
ιBF-rinv {e₂ = done   _ _ N2N_LeiosFetch} ()
ιBF-rinv {e₂ = sndmsg _ _ _} ()
ιBF-rinv {e₂ = rcvmsg _ _ _} ()
ιBF-rinv {e₂ = tx     _ _ _} ()
ιBF-rinv {e₂ = sndack _ _ _} ()
ιBF-rinv {e₂ = rcvack _ _ _} ()
ιBF-rinv {e₂ = ack    _ _ _} ()
ιBF-rinv {e₂ = apiCS  _ _ _} ()
ιBF-rinv {e₂ = apiTS  _ _ _} ()
ιBF-rinv {e₂ = apiKA  _ _ _} ()
ιBF-rinv {e₂ = apiLN  _ _ _} ()
ιBF-rinv {e₂ = apiLF  _ _ _} ()
ιBF-rinv {e₂ = apiLP  _ _ _} ()
ιBF-rinv {e₂ = store  _ _ _} ()
ιBF-rinv {e₂ = env    _ _ _} ()
ιBF-rinv {e₂ = break  _} ()

open import CSP.Laws.DivFree.CountRename ιBF ιBF⁻¹ ιBF-linv ιBF-rinv BFEv-≟ (Net_Api-≟ {Payload})
  using (RenL; rnil; rcons; ren-trace-elim-rel)

-- the label correspondence of a renamed run is the label map
RenL→map : ∀ {ls ls′} → RenL ls ls′ → map renE ls ≡ ls′
RenL→map rnil      = refl
RenL→map (rcons r) = cong (_ ∷_) (RenL→map r)

-- THE BLOCKFETCH CLIENT on `Net_Api`: every block it reports, it received
BFclientA-PA : ∀ l d → PL.PA ChS ChS InP (BFclientA l d)
BFclientA-PA l d = PL.pa λ tr → case ren-trace-elim-rel tr of λ
  { (_ , _ , tr₁ , rl) → subst (PL.Prov ChS ChS InP _) (RenL→map rl) (Prov-map _ (bfClient-prov l d tr₁)) }

-- THE BLOCKFETCH SERVER on `Net_Api`: every block it sends, its thread handed it
BFserverA-PA : ∀ l d → PL.PA ChS ChS InP (BFserverA l d)
BFserverA-PA l d = PL.pa λ tr → case ren-trace-elim-rel tr of λ
  { (_ , _ , tr₁ , rl) → subst (PL.Prov ChS ChS InP _) (RenL→map rl) (Prov-map _ (bfServer-prov l d tr₁)) }

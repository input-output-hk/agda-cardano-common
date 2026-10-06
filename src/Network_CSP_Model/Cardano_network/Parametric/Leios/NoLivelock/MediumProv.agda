{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C (D1-b, shipped route): the MEDIUM HOP of the block
-- chain.  The value a cell delivers was handed to it before: every message
-- the Tx side of a link passes on (`tx`) was `input` earlier
-- (`TxSide-PA`).  Leaves by their menu views, composed by trace
-- projection (`PA-par`), the chain closed (`PA-close`) and the internal
-- handshake hidden (`PA-hide`).  Generic in the carried `Data`.
-- The chain is restricted to the cells whose protocol satisfies `Cl`, so
-- that a cell's provenance never crosses into another protocol's cell
-- (the system instance is `Cl = (_≡ N2N_BlockFetch)`, `MediumRelay`).
-- The Rx side mirrors the Tx side (`RxSide-PA`: every message delivered
-- was `tx` earlier); one link and the whole medium compose the two
-- (`NetOneLink-PA`, `NetworkLink-PA`: every delivered message was `input`).
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)
open import Cardano_network.Base
open import Class.DecEq using (DecEq; _≟_)

module Cardano_network.Parametric.Leios.NoLivelock.MediumProv
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ (Cl : IDs → Set) where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Unit.Polymorphic as UP
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open Params p using (linkConfig; numLinks)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Net p
  using (Net; Net-≟; Link; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack)
open import Cardano_network.Network p Data
  using (NetProc; Input; inputMenu; outputMenu; csSR; csSR-dec; csRS; csRS-dec; csTA; csTA-dec)
import Cardano_network.Network p Data as N
open import Cardano_network.NetworkLink p Data
  using (Transmitterₗ; transmitterMenuₗ; RcvAckₗ; rcvackMenuₗ; Inputsₗ; TxSideₗ
        ; Receiverₗ; receiverMenuₗ; SndAckₗ; sndackMenuₗ; Outputsₗ; RxSideₗ; NetOneLink; NetworkLink)
open import CSP.Operators (Net-≟ {Data}) using (pchoice; Output; Prefix; Ret; Skip; chanSet)
import Semantics.LTS {E = Net Data} {I = ExtI (Net Data)} as L
open import CSP.Laws.DivFree.Loop (Net-≟ {Data}) using (loopStep)
open import CSP.Laws.DivFree.Prov (Net-≟ {Data})

------------------------------------------------------------------------
-- the medium's value chain and its relies
------------------------------------------------------------------------

-- every label that carries a message through a cell of a `Cl` protocol
ChM : L.Event → Data → Set
ChM (L.evLabel _ (input _ _ id) a)  y = Cl id × a ≡ y
ChM (L.evLabel _ (sndmsg _ _ id) a) y = Cl id × a ≡ y
ChM (L.evLabel _ (tx _ _ id) a)     y = Cl id × a ≡ y
ChM (L.evLabel _ (rcvmsg _ _ id) a) y = Cl id × a ≡ y
ChM (L.evLabel _ (output _ _ id) a) y = Cl id × a ≡ y
ChM _                              y = ⊥

-- an input cell relies on what it is given on `input`
InIn : L.Event → Data → Set
InIn (L.evLabel _ (input _ _ id) a) y = Cl id × a ≡ y
InIn _                             y = ⊥

-- the transmitter relies on what it is given on `sndmsg`
InSnd : L.Event → Data → Set
InSnd (L.evLabel _ (sndmsg _ _ id) a) y = Cl id × a ≡ y
InSnd _                              y = ⊥

-- the shape of what a step leaves (a step's obligation and the provenance after it)
StepM : (L.Event → Data → Set) → (Data → Set) → L.Event → NetProc → Set₁
StepM In K x t′ = (∀ {y} → ChM x y → In x y ⊎ K y) × ProvT ChM ChM In (λ y → K y ⊎ ChM x y) t′

------------------------------------------------------------------------
-- the leaves
------------------------------------------------------------------------

-- what a step of an Input cell can be
data InV (l : Link) (d : Dir) (id : IDs) : L.Event → NetProc → Set₁ where
  iv : ∀ x → InV l d id (L.evLabel _ (input l d id) x) (Output (sndmsg l d id) x (Prefix (rcvack l d id) (λ _ → Skip)))

-- the Input inversion
inV : ∀ {l d id x t′} → pchoice (inputMenu l d id) L.─[ L.ev (L.evl x) ]─► t′ → InV l d id x t′
inV {l} {d} {id} (L.sVis {at = _ , input l′ d′ id′} {a = x} refl br) with l′ ≟ l
... | no _ with () ← br
... | yes refl with d′ ≟ d
...   | no _ with () ← br
...   | yes refl with id′ ≟ id
...     | no _ with () ← br
...     | yes refl = subst (InV l d id _) (just-injective br) (iv x)
inV (L.sVis {at = _ , output _ _ _} refl ())
inV (L.sVis {at = _ , sndmsg _ _ _} refl ())
inV (L.sVis {at = _ , rcvmsg _ _ _} refl ())
inV (L.sVis {at = _ , tx _ _ _} refl ())
inV (L.sVis {at = _ , sndack _ _ _} refl ())
inV (L.sVis {at = _ , rcvack _ _ _} refl ())
inV (L.sVis {at = _ , ack _ _ _} refl ())

-- an Input cell forwards (as `sndmsg`) only what it was given
inP : ∀ {l d id K x t′} → InV l d id x t′ → StepM InIn K x t′
inP (iv x) = inj₁ , ProvT-Output _ x (λ c → inj₂ (inj₂ c)) (ProvT-⟶ _ (λ _ ()) (λ _ → ProvT-Ret))

-- THE INPUT LEAF
Input-PA : ∀ l d id → PA ChM ChM InIn (Input l d id)
Input-PA l d id = pa λ tr →
  provIter (loopStep {R = UP.⊤ {0ℓ}} (λ _ → pchoice (inputMenu l d id)))
    (λ _ → ProvT->>= (ProvT-pchoice (λ st → inP (inV st))) (λ _ → ProvT-Ret)) _ tr

-- what a step of the link's transmitter can be
data TrV (l : Link) : L.Event → NetProc → Set₁ where
  tv : ∀ d id x → TrV l (L.evLabel _ (sndmsg l d id) x) (Output (tx l d id) x Skip)

-- the transmitter inversion
trV : ∀ {l x t′} → pchoice (transmitterMenuₗ l) L.─[ L.ev (L.evl x) ]─► t′ → TrV l x t′
trV {l} (L.sVis {at = _ , sndmsg l′ d id} {a = x} refl br) with l′ ≟ l
... | no _     with () ← br
... | yes refl = subst (TrV l _) (just-injective br) (tv d id x)
trV (L.sVis {at = _ , input _ _ _} refl ())
trV (L.sVis {at = _ , output _ _ _} refl ())
trV (L.sVis {at = _ , rcvmsg _ _ _} refl ())
trV (L.sVis {at = _ , tx _ _ _} refl ())
trV (L.sVis {at = _ , sndack _ _ _} refl ())
trV (L.sVis {at = _ , rcvack _ _ _} refl ())
trV (L.sVis {at = _ , ack _ _ _} refl ())

-- the transmitter passes on (as `tx`) only what it was given
trP : ∀ {l K x t′} → TrV l x t′ → StepM InSnd K x t′
trP (tv d id x) = inj₁ , ProvT-Output _ x (λ c → inj₂ (inj₂ c)) ProvT-Ret

-- THE TRANSMITTER LEAF
Tr-PA : ∀ l → PA ChM ChM InSnd (Transmitterₗ l)
Tr-PA l = pa λ tr →
  provIter (loopStep {R = UP.⊤ {0ℓ}} (λ _ → pchoice (transmitterMenuₗ l)))
    (λ _ → ProvT->>= (ProvT-pchoice (λ st → trP (trV st))) (λ _ → ProvT-Ret)) _ tr

-- what a step of the link's ack relay can be
data RaV (l : Link) : L.Event → NetProc → Set₁ where
  rv : ∀ d id u → RaV l (L.evLabel _ (ack l d id) u) (Prefix (rcvack l d id) (λ _ → Skip))

-- the ack-relay inversion
raV : ∀ {l x t′} → pchoice (rcvackMenuₗ l) L.─[ L.ev (L.evl x) ]─► t′ → RaV l x t′
raV {l} (L.sVis {at = _ , ack l′ d id} {a = u} refl br) with l′ ≟ l
... | no _     with () ← br
... | yes refl = subst (RaV l _) (just-injective br) (rv d id u)
raV (L.sVis {at = _ , input _ _ _} refl ())
raV (L.sVis {at = _ , output _ _ _} refl ())
raV (L.sVis {at = _ , sndmsg _ _ _} refl ())
raV (L.sVis {at = _ , rcvmsg _ _ _} refl ())
raV (L.sVis {at = _ , tx _ _ _} refl ())
raV (L.sVis {at = _ , sndack _ _ _} refl ())
raV (L.sVis {at = _ , rcvack _ _ _} refl ())

-- the ack relay carries no message
raP : ∀ {l K x t′} → RaV l x t′ → StepM InSnd K x t′
raP (rv d id u) = (λ ()) , ProvT-⟶ _ (λ _ ()) (λ _ → ProvT-Ret)

-- THE ACK-RELAY LEAF
Ra-PA : ∀ l → PA ChM ChM InSnd (RcvAckₗ l)
Ra-PA l = pa λ tr →
  provIter (loopStep {R = UP.⊤ {0ℓ}} (λ _ → pchoice (rcvackMenuₗ l)))
    (λ _ → ProvT->>= (ProvT-pchoice (λ st → raP (raV st))) (λ _ → ProvT-Ret)) _ tr

------------------------------------------------------------------------
-- the Tx side of a link
------------------------------------------------------------------------

-- a transmitter rely is synchronised (`sndmsg` ∈ csSR), so it never stays one
soloSnd : ∀ {e y} → ¬ InA (chanSet csSR csSR-dec) e → InSnd e y → InIn e y
soloSnd {L.evLabel _ (sndmsg _ _ _) _} ¬m _ = ⊥-elim (¬m UP.tt)
soloSnd {L.evLabel _ (input _ _ _) _}  _ ()
soloSnd {L.evLabel _ (output _ _ _) _} _ ()
soloSnd {L.evLabel _ (rcvmsg _ _ _) _} _ ()
soloSnd {L.evLabel _ (tx _ _ _) _}     _ ()
soloSnd {L.evLabel _ (sndack _ _ _) _} _ ()
soloSnd {L.evLabel _ (rcvack _ _ _) _} _ ()
soloSnd {L.evLabel _ (ack _ _ _) _}    _ ()

-- the Tx side's rely (`input`) is never hidden there
nkSR : ∀ {e y} → InA (chanSet csSR csSR-dec) e → InIn e y → ⊥
nkSR {L.evLabel _ (input _ _ _) _}  () _
nkSR {L.evLabel _ (output _ _ _) _} _ ()
nkSR {L.evLabel _ (sndmsg _ _ _) _} _ ()
nkSR {L.evLabel _ (rcvmsg _ _ _) _} _ ()
nkSR {L.evLabel _ (tx _ _ _) _}     _ ()
nkSR {L.evLabel _ (sndack _ _ _) _} _ ()
nkSR {L.evLabel _ (rcvack _ _ _) _} _ ()
nkSR {L.evLabel _ (ack _ _ _) _}    _ ()

-- the link's input cells
Inputs-PA : ∀ l → PA ChM ChM InIn (Inputsₗ l)
Inputs-PA l = PA-⦀⋆map _ (λ { (d , id) → Input-PA l d id }) (linkConfig l)

-- THE TX SIDE: every message it passes on was input before
TxSide-PA : ∀ l → PA ChM InIn InIn (TxSideₗ l)
TxSide-PA l =
  PA-hide nkSR (PA-close (λ c → c)
    (PA-par (λ _ i → i) soloSnd (λ i _ → i) (Inputs-PA l) (PA-par≡ (Tr-PA l) (Ra-PA l))))

------------------------------------------------------------------------
-- the Rx side of a link
------------------------------------------------------------------------

-- an output cell relies on what it is given on `rcvmsg`
InRcv : L.Event → Data → Set
InRcv (L.evLabel _ (rcvmsg _ _ id) a) y = Cl id × a ≡ y
InRcv _                               y = ⊥

-- the receiver relies on what it is given on `tx`
InTx : L.Event → Data → Set
InTx (L.evLabel _ (tx _ _ id) a) y = Cl id × a ≡ y
InTx _                           y = ⊥

-- what a step of an Output cell can be
data OutV (l : Link) (d : Dir) (id : IDs) : L.Event → NetProc → Set₁ where
  ov : ∀ x → OutV l d id (L.evLabel _ (rcvmsg l d id) x) (Output (output l d id) x (Prefix (sndack l d id) (λ _ → Skip)))

-- the Output inversion
outV : ∀ {l d id x t′} → pchoice (outputMenu l d id) L.─[ L.ev (L.evl x) ]─► t′ → OutV l d id x t′
outV {l} {d} {id} (L.sVis {at = _ , rcvmsg l′ d′ id′} {a = x} refl br) with l′ ≟ l
... | no _ with () ← br
... | yes refl with d′ ≟ d
...   | no _ with () ← br
...   | yes refl with id′ ≟ id
...     | no _ with () ← br
...     | yes refl = subst (OutV l d id _) (just-injective br) (ov x)
outV (L.sVis {at = _ , input _ _ _} refl ())
outV (L.sVis {at = _ , output _ _ _} refl ())
outV (L.sVis {at = _ , sndmsg _ _ _} refl ())
outV (L.sVis {at = _ , tx _ _ _} refl ())
outV (L.sVis {at = _ , sndack _ _ _} refl ())
outV (L.sVis {at = _ , rcvack _ _ _} refl ())
outV (L.sVis {at = _ , ack _ _ _} refl ())

-- an Output cell delivers (as `output`) only what it was given
outP : ∀ {l d id K x t′} → OutV l d id x t′ → StepM InRcv K x t′
outP (ov x) = inj₁ , ProvT-Output _ x (λ c → inj₂ (inj₂ c)) (ProvT-⟶ _ (λ _ ()) (λ _ → ProvT-Ret))

-- THE OUTPUT LEAF
Out-PA : ∀ l d id → PA ChM ChM InRcv (N.Output l d id)
Out-PA l d id = pa λ tr →
  provIter (loopStep {R = UP.⊤ {0ℓ}} (λ _ → pchoice (outputMenu l d id)))
    (λ _ → ProvT->>= (ProvT-pchoice (λ st → outP (outV st))) (λ _ → ProvT-Ret)) _ tr

-- what a step of the link's receiver can be
data RvV (l : Link) : L.Event → NetProc → Set₁ where
  rvv : ∀ d id x → RvV l (L.evLabel _ (tx l d id) x) (Output (rcvmsg l d id) x Skip)

-- the receiver inversion
rvV : ∀ {l x t′} → pchoice (receiverMenuₗ l) L.─[ L.ev (L.evl x) ]─► t′ → RvV l x t′
rvV {l} (L.sVis {at = _ , tx l′ d id} {a = x} refl br) with l′ ≟ l
... | no _     with () ← br
... | yes refl = subst (RvV l _) (just-injective br) (rvv d id x)
rvV (L.sVis {at = _ , input _ _ _} refl ())
rvV (L.sVis {at = _ , output _ _ _} refl ())
rvV (L.sVis {at = _ , sndmsg _ _ _} refl ())
rvV (L.sVis {at = _ , rcvmsg _ _ _} refl ())
rvV (L.sVis {at = _ , sndack _ _ _} refl ())
rvV (L.sVis {at = _ , rcvack _ _ _} refl ())
rvV (L.sVis {at = _ , ack _ _ _} refl ())

-- the receiver passes on (as `rcvmsg`) only what it was given
rvP : ∀ {l K x t′} → RvV l x t′ → StepM InTx K x t′
rvP (rvv d id x) = inj₁ , ProvT-Output _ x (λ c → inj₂ (inj₂ c)) ProvT-Ret

-- THE RECEIVER LEAF
Rv-PA : ∀ l → PA ChM ChM InTx (Receiverₗ l)
Rv-PA l = pa λ tr →
  provIter (loopStep {R = UP.⊤ {0ℓ}} (λ _ → pchoice (receiverMenuₗ l)))
    (λ _ → ProvT->>= (ProvT-pchoice (λ st → rvP (rvV st))) (λ _ → ProvT-Ret)) _ tr

-- what a step of the link's ack sender can be
data SaV (l : Link) : L.Event → NetProc → Set₁ where
  sav : ∀ d id u → SaV l (L.evLabel _ (sndack l d id) u) (Prefix (ack l d id) (λ _ → Skip))

-- the ack-sender inversion
saV : ∀ {l x t′} → pchoice (sndackMenuₗ l) L.─[ L.ev (L.evl x) ]─► t′ → SaV l x t′
saV {l} (L.sVis {at = _ , sndack l′ d id} {a = u} refl br) with l′ ≟ l
... | no _     with () ← br
... | yes refl = subst (SaV l _) (just-injective br) (sav d id u)
saV (L.sVis {at = _ , input _ _ _} refl ())
saV (L.sVis {at = _ , output _ _ _} refl ())
saV (L.sVis {at = _ , sndmsg _ _ _} refl ())
saV (L.sVis {at = _ , rcvmsg _ _ _} refl ())
saV (L.sVis {at = _ , tx _ _ _} refl ())
saV (L.sVis {at = _ , rcvack _ _ _} refl ())
saV (L.sVis {at = _ , ack _ _ _} refl ())

-- the ack sender carries no message
saP : ∀ {l K x t′} → SaV l x t′ → StepM InTx K x t′
saP (sav d id u) = (λ ()) , ProvT-⟶ _ (λ _ ()) (λ _ → ProvT-Ret)

-- THE ACK-SENDER LEAF
Sa-PA : ∀ l → PA ChM ChM InTx (SndAckₗ l)
Sa-PA l = pa λ tr →
  provIter (loopStep {R = UP.⊤ {0ℓ}} (λ _ → pchoice (sndackMenuₗ l)))
    (λ _ → ProvT->>= (ProvT-pchoice (λ st → saP (saV st))) (λ _ → ProvT-Ret)) _ tr

-- an output-cell rely is synchronised (`rcvmsg` ∈ csRS), so it never stays one
soloRcv : ∀ {e y} → ¬ InA (chanSet csRS csRS-dec) e → InRcv e y → InTx e y
soloRcv {L.evLabel _ (rcvmsg _ _ _) _} ¬m _ = ⊥-elim (¬m UP.tt)
soloRcv {L.evLabel _ (input _ _ _) _}  _ ()
soloRcv {L.evLabel _ (output _ _ _) _} _ ()
soloRcv {L.evLabel _ (sndmsg _ _ _) _} _ ()
soloRcv {L.evLabel _ (tx _ _ _) _}     _ ()
soloRcv {L.evLabel _ (sndack _ _ _) _} _ ()
soloRcv {L.evLabel _ (rcvack _ _ _) _} _ ()
soloRcv {L.evLabel _ (ack _ _ _) _}    _ ()

-- the Rx side's rely (`tx`) is never hidden there
nkRS : ∀ {e y} → InA (chanSet csRS csRS-dec) e → InTx e y → ⊥
nkRS {L.evLabel _ (tx _ _ _) _}     () _
nkRS {L.evLabel _ (input _ _ _) _}  _ ()
nkRS {L.evLabel _ (output _ _ _) _} _ ()
nkRS {L.evLabel _ (sndmsg _ _ _) _} _ ()
nkRS {L.evLabel _ (rcvmsg _ _ _) _} _ ()
nkRS {L.evLabel _ (sndack _ _ _) _} _ ()
nkRS {L.evLabel _ (rcvack _ _ _) _} _ ()
nkRS {L.evLabel _ (ack _ _ _) _}    _ ()

-- the link's output cells
Outputs-PA : ∀ l → PA ChM ChM InRcv (Outputsₗ l)
Outputs-PA l = PA-⦀⋆map _ (λ { (d , id) → Out-PA l d id }) (linkConfig l)

-- THE RX SIDE: every message it delivers was `tx` before
RxSide-PA : ∀ l → PA ChM InTx InTx (RxSideₗ l)
RxSide-PA l =
  PA-hide nkRS (PA-close (λ c → c)
    (PA-par soloRcv (λ _ i → i) (λ _ i → i) (Outputs-PA l) (PA-par≡ (Rv-PA l) (Sa-PA l))))

------------------------------------------------------------------------
-- one link, and the whole medium
------------------------------------------------------------------------

-- a Tx-side rely (`input`) is a chain label
inCh : ∀ {e y} → InIn e y → ChM e y
inCh {L.evLabel _ (input _ _ _) _}  c = c
inCh {L.evLabel _ (output _ _ _) _} ()
inCh {L.evLabel _ (sndmsg _ _ _) _} ()
inCh {L.evLabel _ (rcvmsg _ _ _) _} ()
inCh {L.evLabel _ (tx _ _ _) _}     ()
inCh {L.evLabel _ (sndack _ _ _) _} ()
inCh {L.evLabel _ (rcvack _ _ _) _} ()
inCh {L.evLabel _ (ack _ _ _) _}    ()

-- an Rx-side rely (`tx`) is a chain label
txCh : ∀ {e y} → InTx e y → ChM e y
txCh {L.evLabel _ (tx _ _ _) _}     c = c
txCh {L.evLabel _ (input _ _ _) _}  ()
txCh {L.evLabel _ (output _ _ _) _} ()
txCh {L.evLabel _ (sndmsg _ _ _) _} ()
txCh {L.evLabel _ (rcvmsg _ _ _) _} ()
txCh {L.evLabel _ (sndack _ _ _) _} ()
txCh {L.evLabel _ (rcvack _ _ _) _} ()
txCh {L.evLabel _ (ack _ _ _) _}    ()

-- a receiver rely is synchronised (`tx` ∈ csTA), so it never stays one
soloTx : ∀ {e y} → ¬ InA (chanSet csTA csTA-dec) e → InTx e y → InIn e y
soloTx {L.evLabel _ (tx _ _ _) _}     ¬m _ = ⊥-elim (¬m UP.tt)
soloTx {L.evLabel _ (input _ _ _) _}  _ ()
soloTx {L.evLabel _ (output _ _ _) _} _ ()
soloTx {L.evLabel _ (sndmsg _ _ _) _} _ ()
soloTx {L.evLabel _ (rcvmsg _ _ _) _} _ ()
soloTx {L.evLabel _ (sndack _ _ _) _} _ ()
soloTx {L.evLabel _ (rcvack _ _ _) _} _ ()
soloTx {L.evLabel _ (ack _ _ _) _}    _ ()

-- the link's rely (`input`) is never hidden there
nkTA : ∀ {e y} → InA (chanSet csTA csTA-dec) e → InIn e y → ⊥
nkTA {L.evLabel _ (input _ _ _) _}  () _
nkTA {L.evLabel _ (output _ _ _) _} _ ()
nkTA {L.evLabel _ (sndmsg _ _ _) _} _ ()
nkTA {L.evLabel _ (rcvmsg _ _ _) _} _ ()
nkTA {L.evLabel _ (tx _ _ _) _}     _ ()
nkTA {L.evLabel _ (sndack _ _ _) _} _ ()
nkTA {L.evLabel _ (rcvack _ _ _) _} _ ()
nkTA {L.evLabel _ (ack _ _ _) _}    _ ()

-- ONE LINK: every message it delivers was input before
NetOneLink-PA : ∀ l → PA ChM InIn InIn (NetOneLink l)
NetOneLink-PA l =
  PA-hide nkTA (PA-close (λ c → c)
    (PA-par (λ _ i → i) soloTx (λ i _ → i) (PA-weak (λ o → o) (λ i → i) inCh (TxSide-PA l))
                                            (PA-weak (λ o → o) (λ i → i) txCh (RxSide-PA l))))

-- THE MEDIUM: every message it delivers was input before
NetworkLink-PA : PA ChM InIn InIn NetworkLink
NetworkLink-PA = PA-⦀Fin numLinks NetOneLink NetOneLink-PA

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C, Task 9b: THE SYSTEM PROVENANCE (D1-b).
-- Every block a chain label of the system over a medium (`SysOver`; Stage C's
-- `rawSys2` and Stage L's `rawL`) carries is one an earlier chain
-- label of the same trace carried, or a FORGE's — the only rely left at
-- system level is `envForge` (`Fg`).  Composition: at every `∥` the rely
-- is the formal one of `PA-par` (`I₁ ⟨ A ⟩ I₂`: a solo rely of a side, or
-- a rely of both), so every side condition is free; ONE classification
-- (`toFg`, by channel) shows the system's formal rely is a forge.
-- `sys-inX` reads it out for the stores: every chain-label block of the
-- trace lies in `fvals (labels s)`, the blocks forged in it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; VB; AllV; HP)

module Cardano_network.Parametric.Leios.NoLivelock.ProvSys
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) (U : List (VB m)) (allV : AllV m U) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
open Topology tP using (Node)


open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Sum using ([_,_])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (length-++)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (id)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Net pP
open import Cardano_network.Data pP using (Payload; blockFetch; MsgBlock)
open import Cardano_network.NetCommon pP using (ioES)
open import Cardano_network.ApiAlphabet pP using (apiES)
open import Cardano_network.Params using (module Params)
open Params pP using (Block; decBlock)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (EventSet; Par; Skip; _⦀_; _∥⇘_⇙_; ⦀Fin⁺)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels; AllL; []; _∷_; AllL-map)
open import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload})
  using (InA; Kn; Prov; Prov-weak; Prov-close; Prov→All; PA; pa; runA; PA-par; PA-par≡; PA-Ret)
open import CSP.Laws.DivFree.ProvMore (Net_Api-≟ {Payload}) using (PA-if; PA-⦀⁺; PA-⦀Fin⁺)
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic pP tP apiES using (storeES)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic pP lpP tP apiES vo using (memberOf; nodeLogicL; st₀)
open import Cardano_network.Parametric.Node pP tP apiES using (bundleAtWith; nodeWith)
open import Cardano_network.Parametric.Topology using (module Topology; opposite)
open Topology tP using (endpointsOf)
open import Cardano_network.Parametric.Leios.PeersP pP using (Proc; clientPeerP; serverPeerP; nodeBundleP)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF pP using (ChS; InP; msgBlk; BFclientA-PA; BFserverA-PA)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerKA pP using (kaClientA-PA; kaServerA-PA)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerCS pP using (csClientA-PA; csServerA-PA)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerTS pP using (tsClientA-PA; tsServerA-PA)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLNP pP using (lnpClientA-PA; lnpServerA-PA)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP pP using (lfpClientA-PA; lfpServerA-PA)
open import Cardano_network.Parametric.Leios.NoLivelock.MediumRelay pP using (InM)
open import Cardano_network.Parametric.Leios.NoLivelock.ThreadsProv k m tP vo using (InT; threadsL-PA)
open import Cardano_network.Parametric.Leios.NoLivelock.StoresProv k m tP vo U allV using (InSt; storesL-PA; InX; dt)

------------------------------------------------------------------------
-- the forges
------------------------------------------------------------------------

-- the block a label forges (one non-empty clause: a forge)
fv : Event → List Block
fv (evLabel _ (env _ _ envForge) (_ , b)) = b ∷ []
fv _                                      = []

-- the blocks forged along a label list
fvals : List Event → List Block
fvals []       = []
fvals (e ∷ ls) = fv e ++ fvals ls

-- 1 on a forge
cFg : Event → ℕ
cFg e = length (fv e)

-- THE SYSTEM RELY: the label forges the block (non-empty only on `envForge`, through `fv`)
Fg : Event → Block → Set
Fg e y = Any (y ≡_) (fv e)

-- as many forged blocks as forges
length-fvals : ∀ ls → length (fvals ls) ≡ Σc cFg ls
length-fvals []       = refl
length-fvals (e ∷ ls) = trans (length-++ (fv e)) (cong (cFg e +_) (length-fvals ls))

-- a forge's block is among the blocks forged
Kn→fvals : ∀ {ls b} → Kn Fg ls b → memberOf ⦃ decBlock ⦄ b (fvals ls) ≡ true
Kn→fvals {e ∷ ls} (inj₁ f) = memL (fv e) (fvals ls) f
  where
    -- membership in a prefix
    memL : ∀ {b} xs ys → Any (b ≡_) xs → memberOf ⦃ decBlock ⦄ b (xs ++ ys) ≡ true
    memL (x ∷ xs) ys (here refl) = cong (λ z → z ∨ memberOf ⦃ decBlock ⦄ x (xs ++ ys)) (dt (DecEq._≟_ decBlock x x))
    memL {b} (x ∷ xs) ys (there a) = trans (cong (⌊ DecEq._≟_ decBlock x b ⌋ ∨_) (memL xs ys a)) (∨-zeroʳ _)
Kn→fvals {e ∷ ls} (inj₂ k) = memR (fv e) (Kn→fvals k)
  where
    -- membership in a suffix
    memR : ∀ {b ys} xs → memberOf ⦃ decBlock ⦄ b ys ≡ true → memberOf ⦃ decBlock ⦄ b (xs ++ ys) ≡ true
    memR []       m = m
    memR {b} (x ∷ xs) m = trans (cong (⌊ DecEq._≟_ decBlock x b ⌋ ∨_) (memR xs m)) (∨-zeroʳ _)

------------------------------------------------------------------------
-- the system provenance
------------------------------------------------------------------------

-- the rely of a parallel composition: a solo rely of either side, or a rely of both
_⟨_⟩_ : (Event → Block → Set) → EventSet → (Event → Block → Set) → Event → Block → Set
(I₁ ⟨ A ⟩ I₂) e x = (¬ InA A e × I₁ e x) ⊎ ((¬ InA A e × I₂ e x) ⊎ (I₁ e x × I₂ e x))

-- composition through `Par`, every side condition discharged formally
PA-par′ : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓs} {A : EventSet} {merge : R₁ → R₂ → R₀}
          {P : _} {Q : _} {I₁ I₂ : Event → Block → Set}
        → PA ChS ChS I₁ P → PA ChS ChS I₂ Q → PA ChS ChS (I₁ ⟨ A ⟩ I₂) (Par A merge P Q)
PA-par′ = PA-par (λ m i → inj₁ (m , i)) (λ m i → inj₂ (inj₁ (m , i))) (λ i j → inj₂ (inj₂ (i , j)))

-- the logic's rely: threads against stores
LR : Event → Block → Set
LR = InT ⟨ storeES ⟩ InSt

-- a node's rely: bundles against logic
NR : Event → Block → Set
NR = InP ⟨ apiES ⟩ LR

-- the system's rely: medium against nodes
SR : Event → Block → Set
SR = InM ⟨ ioES ⟩ NR

-- the logic's provenance
logic-PA : ∀ n → PA ChS ChS LR (nodeLogicL n st₀)
logic-PA n = PA-par′ (threadsL-PA n) (storesL-PA n)

-- every client instance's provenance
pcP : ∀ l d id → PA ChS ChS InP (clientPeerP l d id)
pcP l d N2N_KeepAlive    = kaClientA-PA l d
pcP l d N2N_ChainSync    = csClientA-PA l d
pcP l d N2N_BlockFetch   = BFclientA-PA l d
pcP l d N2N_TxSubmission = tsClientA-PA l d
pcP l d N2N_LeiosNotify  = lnpClientA-PA l d
pcP l d N2N_LeiosFetch   = lfpClientA-PA l d

-- every server instance's provenance
psP : ∀ l d id → PA ChS ChS InP (serverPeerP l d id)
psP l d N2N_KeepAlive    = kaServerA-PA l d
psP l d N2N_ChainSync    = csServerA-PA l d
psP l d N2N_BlockFetch   = BFserverA-PA l d
psP l d N2N_TxSubmission = tsServerA-PA l d
psP l d N2N_LeiosNotify  = lnpServerA-PA l d
psP l d N2N_LeiosFetch   = lfpServerA-PA l d

-- one endpoint's bundle (the twelve instances, as `TauAssembly.bundle-R`)
bundle-PA : ∀ l cl sv → PA ChS ChS InP (nodeBundleP l cl sv)
bundle-PA l cl sv =
  PA-par≡ (pk lo N2N_KeepAlive)    (PA-par≡ (pk hi N2N_KeepAlive)
  (PA-par≡ (pk lo N2N_ChainSync)   (PA-par≡ (pk hi N2N_ChainSync)
  (PA-par≡ (pk lo N2N_BlockFetch)  (PA-par≡ (pk hi N2N_BlockFetch)
  (PA-par≡ (pk lo N2N_TxSubmission) (PA-par≡ (pk hi N2N_TxSubmission)
  (PA-par≡ (pk lo N2N_LeiosNotify) (PA-par≡ (pk hi N2N_LeiosNotify)
  (PA-par≡ (pk lo N2N_LeiosFetch)  (PA-par≡ (pk hi N2N_LeiosFetch) PA-Ret)))))))))))
  where
    -- one configured instance, dispatched by direction
    pk : ∀ d id → PA ChS ChS InP (if ⌊ d ≟ cl ⌋ then clientPeerP l d id else if ⌊ d ≟ sv ⌋ then serverPeerP l d id else Skip)
    pk d id = PA-if ⌊ d ≟ cl ⌋ (pcP l d id) (PA-if ⌊ d ≟ sv ⌋ (psP l d id) PA-Ret)

-- a node's provenance
node-PA : ∀ n → PA ChS ChS NR (nodeWith nodeBundleP n (nodeLogicL n st₀))
node-PA n = PA-par′ (PA-⦀⁺ (bAt (proj₁ (endpointsOf n))) (map⁺ (All.universal bAt (proj₂ (endpointsOf n))))) (logic-PA n)
  where
    -- one incident endpoint's bundle
    bAt : ∀ ld → PA ChS ChS InP (bundleAtWith nodeBundleP ld)
    bAt ld = bundle-PA (proj₁ ld) (proj₂ ld) (opposite (proj₂ ld))

-- the system over a medium: the medium against every node of the line on `ioES`
SysOver : Proc → Proc
SysOver med = med ∥⇘ ioES ⇙ ⦀Fin⁺ (Topology.numNodes-1 tP) (λ n → nodeWith nodeBundleP n (nodeLogicL n st₀))

-- the system's provenance, under its formal rely, from the medium's
sys-PA : ∀ {med} → PA ChS ChS InM med → PA ChS ChS SR (SysOver med)
sys-PA {med} mp = PA-par′ mp (PA-⦀Fin⁺ (Topology.numNodes-1 tP) _ node-PA)

-- eliminating a formal rely
⟨⟩-elim : ∀ {I₁ I₂ : Event → Block → Set} {A e x} {Z : Set} → (¬ InA A e → I₁ e x → Z) → (¬ InA A e → I₂ e x → Z)
        → (I₁ e x → I₂ e x → Z) → (I₁ ⟨ A ⟩ I₂) e x → Z
⟨⟩-elim f g h (inj₁ (m , i))         = f m i
⟨⟩-elim f g h (inj₂ (inj₁ (m , j)))  = g m j
⟨⟩-elim f g h (inj₂ (inj₂ (i , j)))  = h i j

-- eliminating the system's, a node's and the logic's formal rely
srE : ∀ {e x} {Z : Set} → (¬ InA ioES e → InM e x → Z) → (¬ InA ioES e → NR e x → Z) → (InM e x → NR e x → Z) → SR e x → Z
srE = ⟨⟩-elim {InM} {NR} {ioES}

-- … a node's
nrE : ∀ {e x} {Z : Set} → (¬ InA apiES e → InP e x → Z) → (¬ InA apiES e → LR e x → Z) → (InP e x → LR e x → Z) → NR e x → Z
nrE = ⟨⟩-elim {InP} {LR} {apiES}

-- … the logic's
lrE : ∀ {e x} {Z : Set} → (¬ InA storeES e → InT e x → Z) → (¬ InA storeES e → InSt e x → Z) → (InT e x → InSt e x → Z) → LR e x → Z
lrE = ⟨⟩-elim {InT} {InSt} {storeES}

-- a label no base rely holds of
SR⊥ : ∀ e {x} {Z : Set} → (∀ {y} → InM e y → ⊥) → (∀ {y} → InP e y → ⊥) → (∀ {y} → InT e y → ⊥) → (∀ {y} → InSt e y → ⊥)
    → SR e x → Z
SR⊥ e m p t u r = ⊥-elim (srE (λ _ → m) (λ _ → nrE (λ _ → p) (λ _ → lrE (λ _ → t) (λ _ → u) (λ i _ → t i)) (λ i _ → p i))
                              (λ i _ → m i) r)

-- a wire input: only the medium's rely can hold, and it is synchronised with no node rely
SRio : ∀ e {x} {Z : Set} → InA ioES e → (∀ {y} → InP e y → ⊥) → (∀ {y} → InT e y → ⊥) → (∀ {y} → InSt e y → ⊥)
     → SR e x → Z
SRio e io p t u r = ⊥-elim (srE (λ n _ → n io) (λ n _ → n io)
                              (λ _ → nrE (λ _ → p) (λ _ → lrE (λ _ → t) (λ _ → u) (λ i _ → t i)) (λ i _ → p i)) r)

-- a wire output: not the medium's rely, and synchronised
SRout : ∀ e {x} {Z : Set} → InA ioES e → (∀ {y} → InM e y → ⊥) → SR e x → Z
SRout e io m r = ⊥-elim (srE (λ n _ → n io) (λ n _ → n io) (λ i _ → m i) r)

-- an api label: medium and logic-solo relies are out; a peer and the logic never share one
SRapi : ∀ e {x} {Z : Set} → InA apiES e → (∀ {y} → InM e y → ⊥) → (∀ {y} → InP e y → LR e y → ⊥) → SR e x → Z
SRapi e api m pl r = ⊥-elim (srE (λ _ → m) (λ _ → nrE (λ n _ → n api) (λ n _ → n api) pl) (λ i _ → m i) r)

-- a store label: only threads and stores together can rely on it
SRst : ∀ e {x} → InA storeES e → (∀ {y} → InM e y → ⊥) → (∀ {y} → InP e y → ⊥) → (∀ {y} → InT e y → InSt e y → Fg e y)
     → SR e x → Fg e x
SRst e st m p tu = srE (λ _ i → ⊥-elim (m i))
                     (λ _ → nrE (λ _ i → ⊥-elim (p i)) (λ _ → lrE (λ n _ → ⊥-elim (n st)) (λ n _ → ⊥-elim (n st)) tu)
                              (λ i _ → ⊥-elim (p i)))
                     (λ i _ → ⊥-elim (m i))

-- THE CLASSIFICATION: the system's formal rely holds only of a forge
toFg : ∀ {e x} → SR e x → Fg e x
toFg {e@(evLabel _ (input _ _ _) _)} {x}  = SRio e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (output _ _ _) _)} {x} = SRout e {x} _ (λ ())
toFg {e@(evLabel _ (sndmsg _ _ _) _)} {x} = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (rcvmsg _ _ _) _)} {x} = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (tx _ _ _) _)} {x}     = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (sndack _ _ _) _)} {x} = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (rcvack _ _ _) _)} {x} = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (ack _ _ _) _)} {x}    = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (done _ _ _) _)} {x}   = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (apiCS _ _ _) _)} {x}  = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (apiTS _ _ _) _)} {x}  = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (apiKA _ _ _) _)} {x}  = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (apiLN _ _ _) _)} {x}  = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (apiLF _ _ _) _)} {x}  = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (apiLP _ _ _) _)} {x}  = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (break _) _)} {x}      = SR⊥ e {x} (λ ()) (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (apiBF _ _ sendBFBlock) _)} {x}        = SRapi e {x} _ (λ ()) (λ {y} _ → lrE {e} {y} (λ _ ()) (λ _ ()) (λ ()))
toFg {e@(evLabel _ (apiBF _ _ recvBFBlock) _)} {x}        = SRapi e {x} _ (λ ()) (λ ())
toFg {e@(evLabel _ (apiBF _ _ sendBFRequestRange) _)} {x} = SRapi e {x} _ (λ ()) (λ ())
toFg {e@(evLabel _ (apiBF _ _ sendBFClientDone) _)} {x}   = SRapi e {x} _ (λ ()) (λ ())
toFg {e@(evLabel _ (apiBF _ _ sendBFStartBatch) _)} {x}   = SRapi e {x} _ (λ ()) (λ ())
toFg {e@(evLabel _ (apiBF _ _ sendBFNoBlocks) _)} {x}     = SRapi e {x} _ (λ ()) (λ ())
toFg {e@(evLabel _ (apiBF _ _ sendBFBatchDone) _)} {x}    = SRapi e {x} _ (λ ()) (λ ())
toFg {e@(evLabel _ (apiBF _ _ reqBFRange) _)} {x}         = SRapi e {x} _ (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ stPut) _)} {x}         = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ stGet) _)} {x}         = SRst e {x} _ (λ ()) (λ ()) (λ _ ())
toFg {e@(evLabel _ (store _ _ (stGetAt _)) _)} {x}   = SRst e {x} _ (λ ()) (λ ()) (λ _ ())
toFg {e@(evLabel _ (store _ _ stPutEB) _)} {x}       = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ (stGetEBAt _)) _)} {x} = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ stPutBody) _)} {x}     = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ (stGetBody _)) _)} {x} = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ stPutTx) _)} {x}       = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ (stGetTxAt _)) _)} {x} = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ stPutVote) _)} {x}     = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ (stGetVoteAt _)) _)} {x} = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ stCert) _)} {x}        = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ (stGetTx _)) _)} {x}   = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (store _ _ (stHasCert _)) _)} {x} = SRst e {x} _ (λ ()) (λ ()) (λ ())
toFg {e@(evLabel _ (env _ _ envForge) _)} {x}        = SRst e {x} _ (λ ()) (λ ()) (λ { refl _ → here refl })
toFg {e@(evLabel _ (env _ _ envSubmit) _)} {x}       = SRst e {x} _ (λ ()) (λ ()) (λ ())

-- THE SYSTEM PROVENANCE: the only rely left is a forge
sys-prov : ∀ {med} → PA ChS ChS InM med → ∀ {s W} → SysOver med ⟹⟨ s ⟩ W → Prov ChS ChS Fg (λ _ → ⊥) (labels s)
sys-prov mp {s} tr = Prov-weak (labels s) (λ c → c) toFg (λ c → c) (λ ()) (runA (sys-PA mp) {K = λ _ → ⊥} tr)

-- … read out for the stores: every block on any chain label of the trace was forged in it
sys-inX : ∀ {med} → PA ChS ChS InM med → ∀ {s W} → SysOver med ⟹⟨ s ⟩ W → AllL (InX (fvals (labels s))) (labels s)
sys-inX mp {s} tr =
  AllL-map (λ f c → [ (λ ()) , Kn→fvals ] (f c)) (Prov→All (labels s) (Prov-close {K′ = λ _ → ⊥} (labels s) (λ c → c) (λ ()) (sys-prov mp tr)))

-- sanity: the chain relation holds on every chain kind (so no guarantee is vacuous)
chs-put : ∀ {l d b} → ChS (evLabel _ (store l d stPut) b) b
chs-put = refl

-- … a read
chs-get : ∀ {l d b} → ChS (evLabel _ (store l d stGet) b) b
chs-get = refl

-- … an indexed read
chs-getAt : ∀ {l d k b} → ChS (evLabel _ (store l d (stGetAt k)) b) b
chs-getAt = refl

-- … a served block
chs-sendBF : ∀ {l d b} → ChS (evLabel _ (apiBF l d sendBFBlock) b) b
chs-sendBF = refl

-- … a delivered block
chs-recvBF : ∀ {l d b} → ChS (evLabel _ (apiBF l d recvBFBlock) b) b
chs-recvBF = refl

-- … a BlockFetch wire input
chs-wireIn : ∀ {l d t m n b} → ChS (evLabel _ (input l d N2N_BlockFetch) (t , m , n , blockFetch (MsgBlock b))) b
chs-wireIn = refl

-- … a BlockFetch wire output
chs-wireOut : ∀ {l d t m n b} → ChS (evLabel _ (output l d N2N_BlockFetch) (t , m , n , blockFetch (MsgBlock b))) b
chs-wireOut = refl

-- … a forge
chs-forge : ∀ {l d me b} → ChS (evLabel _ (env l d envForge) (me , b)) b
chs-forge = refl

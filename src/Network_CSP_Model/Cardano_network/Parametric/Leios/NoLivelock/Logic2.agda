{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C/L: the node LOGIC's counting facts.
--   * `cls`     — ONE classification of every label, by channel: which
--                 weights vanish off the api / io / store alphabets, the
--                 per-label ≤ 1 facts, the environment weights below χ̄
--   * threads   — the thread summaries composed over `THn` (`thrN`: the
--                 five node threads, then `thr10` folded over every
--                 endpoint, `slk`): the event count against the trigger weight
--                 `TW`, every relay group's commands against its owner's
--                 bound (non-owners vanish by `ThreadAlpha`), no wire io
--   * stores    — every read below its store's bound, at most three
--                 certificates (`storesF`)
--   * `logicFN` — threads against stores: the logic's H-labels, api
--                 labels, wire inputs and commands, on its own labels
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; VB; AllV; HP)

module Cardano_network.Parametric.Leios.NoLivelock.Logic2
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) (U : List (VB m)) (allV : AllV m U) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
-- the hidden set of this family member
HK = HP k m
open Topology tP using (Node; endpointsOf)


open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; reverse; map)
open import Data.Unit using (⊤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; *-monoʳ-≤; +-identityʳ; m≤m+n; m≤n+m; ≤ᵇ⇒≤; +-assoc; +-comm; *-distribˡ-+)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (Fin)
import Data.Unit.Polymorphic as UP
open import Level using (0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Class.DecEq using (DecEq)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Parametric.Topology using (opposite)
open import Cardano_network.Net pP
open import Cardano_network.Data pP using (Payload)
open import Cardano_network.NetCommon pP using (ioES)
open import Cardano_network.ApiAlphabet pP using (apiES)
open import Cardano_network.Params using (module Params)
open Params pP using (Block)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel; Event√; evl; √)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_⦀_; _∥⇘_⇙_; Prefix; Output; ⦀⁺)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
  using (Σc; labels; AllL; []; _∷_; AllL-map; AnyE; IsE; #e; AllT; AllT-Ret; AllT-⟶; AllT-Output; AllT-□; AllT-Stop)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload})
  using (Σc-⦀; Σc-sync; χ; χ̄; ≤-≡; +-inter; AnyE-parL; AnyE-parR; AnyE-sync; AllL-parL; AllL-parR)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc-par; Σc-parL; Σc-parR)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload}) using (Par-trace-elim; ParInter; pnil; psync; psoloL; psoloR; p√)
open import CSP.Laws.DivFree.ParLabels (Net_Api-≟ {Payload}) using (subR; labR; AllL-⦀)
open import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) using (InA)
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic pP tP apiES using (storeES; forgeEv; putEv; getEv; offerHeld; clientLoop)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic pP lpP tP apiES vo
  using ( serverLoopL; lnServerLoopL; ebIndex; voter; bodyOfferLoop; voteOfferBody; voteOfferLoop; tsServeBody; tsServe
        ; forgeL; submit; certSink; lnClientLoopL; ebServeLoop; ebTxsServeLoop; tsPull; endpointThreadsL
        ; blockStoreL; ebStore; bodyStore; mempool; voteStore; voteStep; storeStepL; getAtEv; getVoteAtEv; getTxAtEv; allThreadsL
        ; nodeLogicL; st₀ )
open import Cardano_network.Parametric.Leios.PeersP pP using (Proc; nodeBundleP)
open import Cardano_network.Parametric.Node pP tP apiES using (linkBundlesWith; bundleAtWith; nodeWith)
open import Cardano_network.Parametric.Leios.NoLivelock.Weights pP
open import Cardano_network.Parametric.Leios.NoLivelock.MediumRelay pP using (WireW; wO; wI)
open import Cardano_network.Parametric.Leios.NoLivelock.Threads k m tP vo
  using ( IsGetAt; IsGetVoteAt; IsGetTxAt; cForge; cSubmit; cCert; cLnRep; ℓLnRep; loopAll; Σc-≤; iVs; iTs; iHs
        ; serverLoopL-count; lnServerLoopL-count; ebIndex-count; voter-count; bodyOfferLoop-count; voteOfferLoop-count
        ; tsServe-count; forgeL-count; submit-count; certSink-count; clientLoop-count; lnClientLoopL-count
        ; ebServeLoop-count; ebTxsServeLoop-count; tsPull-count
        ; voteOffer-emits; tsServe-emits; fetchTxs-emits; serveTxs-emits; serverLoopL-cmd; lnServerLoopL-cmd
        ; bodyOfferLoop-cmd; fetchTxs-req )
open import Cardano_network.Parametric.Leios.NoLivelock.ThreadAlpha k m tP vo
  using (Grp; gCS; gAnn; gOff; gVot; gReq; gBTx; gTS; gw; gm; fw; Alw
        ; forgeL-α; ebIndex-α; voter-α; submit-α; certSink-α; clientLoop-α; serverLoopL-α; lnClientLoopL-α
        ; lnServerLoopL-α; bodyOfferLoop-α; voteOfferLoop-α; ebServeLoop-α; ebTxsServeLoop-α; tsPull-α; tsServe-α)
  renaming (IsZ to IsZt)
open import Cardano_network.Parametric.Leios.NoLivelock.Stores k m tP vo U allV
  using (cF; mempool-reads; voteStore-reads; voteStore-certs; eb-All; body-All; mem-All; vote-All; oiAll)
open import Cardano_network.Parametric.Leios.NoLivelock.StoresProv k m tP vo U allV
  using (Σc-+; Σc-0; InX; ROkX; blockStore-reads-prov
        ; blockStoreL-alph; ebStore-alph; bodyStore-alph; mempool-alph; voteStore-alph)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerAlpha k m tP vo U allV
  using (Gr; gRF; gLN; gTQ; gBT; gBQ; rep; cmd; ww; one; IsZ; isZ≡; allL; zipL; Σc-cong; ≤0; Rl; rl-⦀; bundleG; bundleB; gc; gd)
  renaming (gTS to grTS)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvSys k m tP vo U allV using (cFg)

------------------------------------------------------------------------
-- the classification of every label
------------------------------------------------------------------------

-- the api weights vanish (every group's reports and commands, and `cApi`)
OffA : Event → Set
OffA e = IsZ (rep gRF e) × (IsZ (rep grTS e) × (IsZ (rep gLN e) × (IsZ (rep gTQ e) × (IsZ (rep gBT e) × (IsZ (rep gBQ e)
       × (IsZ (cmd gRF e) × (IsZ (cmd grTS e) × (IsZ (cmd gLN e) × (IsZ (cmd gTQ e) × (IsZ (cmd gBT e) × (IsZ (cmd gBQ e)
       × IsZ (cApi e))))))))))))

-- a read of any store pointer
Rd : ℕ → Event → Set
Rd j e = IsGetAt j e ⊎ (IsGetVoteAt j e ⊎ IsGetTxAt j e)

-- what every label satisfies, by channel
record Cls (e : Event) : Set where
  constructor cl
  field
    oA : ¬ InA apiES e → OffA e
    oI : ∀ w → ¬ InA ioES e → wI w e ≡ 0 × wO w e ≡ 0
    oN : cIn e ≡ 0 → ∀ w → wI w e ≡ 0
    o1 : T (cApi e ≤ᵇ 1) × T (χ HK e ≤ᵇ 1)
    oV : T (cForge e + cSubmit e ≤ᵇ χ̄ HK e) × (T (cF e ≤ᵇ χ̄ HK e) × T (cFg e ≤ᵇ χ̄ HK e))
    oS : ¬ InA storeES e → cCert e ≡ 0
    oR : ∀ {j} → Rd j e → InA storeES e

-- an impossible read
rd⊥ : ∀ {A : Set} → ⊥ ⊎ (⊥ ⊎ ⊥) → A
rd⊥ (inj₁ ())
rd⊥ (inj₂ (inj₁ ()))
rd⊥ (inj₂ (inj₂ ()))

-- THE CLASSIFICATION
cls : ∀ e → Cls e
cls (evLabel _ (input _ _ _) _)  = cl (λ _ → _) (λ _ m → ⊥-elim (m _)) (λ ()) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (output _ _ _) _) = cl (λ _ → _) (λ _ m → ⊥-elim (m _)) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (sndmsg _ _ _) _) = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (rcvmsg _ _ _) _) = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (tx _ _ _) _)     = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (sndack _ _ _) _) = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (rcvack _ _ _) _) = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (ack _ _ _) _)    = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (break _) _)      = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (done _ _ _) _)   = cl (λ m → ⊥-elim (m _)) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (apiCS _ _ _) _)  = cl (λ m → ⊥-elim (m _)) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (apiBF _ _ _) _)  = cl (λ m → ⊥-elim (m _)) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (apiTS _ _ _) _)  = cl (λ m → ⊥-elim (m _)) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (apiKA _ _ _) _)  = cl (λ m → ⊥-elim (m _)) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (apiLN _ _ _) _)  = cl (λ m → ⊥-elim (m _)) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (apiLF _ _ _) _)  = cl (λ m → ⊥-elim (m _)) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (apiLP _ _ _) _)  = cl (λ m → ⊥-elim (m _)) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ _ → refl) rd⊥
cls (evLabel _ (store _ _ _) _)  = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ m → ⊥-elim (m _)) (λ _ → _)
cls (evLabel _ (env _ _ envForge) _)  = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ m → ⊥-elim (m _)) (λ _ → _)
cls (evLabel _ (env _ _ envSubmit) _) = cl (λ _ → _) (λ _ _ → refl , refl) (λ _ _ → refl) _ _ (λ m → ⊥-elim (m _)) (λ _ → _)

-- a group's reports vanish off the api alphabet
offRep : ∀ g e → ¬ InA apiES e → rep g e ≡ 0
offRep gRF  e m = isZ≡ (proj₁ (Cls.oA (cls e) m))
offRep grTS e m = isZ≡ (proj₁ (proj₂ (Cls.oA (cls e) m)))
offRep gLN  e m = isZ≡ (proj₁ (proj₂ (proj₂ (Cls.oA (cls e) m))))
offRep gTQ  e m = isZ≡ (proj₁ (proj₂ (proj₂ (proj₂ (Cls.oA (cls e) m)))))
offRep gBT  e m = isZ≡ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (Cls.oA (cls e) m))))))
offRep gBQ  e m = isZ≡ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Cls.oA (cls e) m)))))))

-- … its commands
offCmd : ∀ g e → ¬ InA apiES e → cmd g e ≡ 0
offCmd gRF  e m = isZ≡ (proj₁ (proj₂⁶ (Cls.oA (cls e) m)))
  where
    -- six steps right
    proj₂⁶ : ∀ {A B C D F G H : Set} → A × (B × (C × (D × (F × (G × H))))) → H
    proj₂⁶ z = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ z)))))
offCmd grTS e m = isZ≡ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Cls.oA (cls e) m)))))))))
offCmd gLN  e m = isZ≡ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Cls.oA (cls e) m))))))))))
offCmd gTQ  e m = isZ≡ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Cls.oA (cls e) m)))))))))))
offCmd gBT  e m = isZ≡ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Cls.oA (cls e) m))))))))))))
offCmd gBQ  e m = isZ≡ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Cls.oA (cls e) m)))))))))))))

-- … and `cApi`
offApi : ∀ e → ¬ InA apiES e → cApi e ≡ 0
offApi e m = isZ≡ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Cls.oA (cls e) m)))))))))))))

------------------------------------------------------------------------
-- generic helpers
------------------------------------------------------------------------

-- the unit weight
𝟙 : Event → ℕ
𝟙 _ = 1

-- the zero weight
z0 : Event → ℕ
z0 _ = 0

-- the zero weight sums to zero
Σz : ∀ ls → Σc z0 ls ≡ 0
Σz []       = refl
Σz (e ∷ ls) = Σz ls

-- the event count is the unit weight
#e≡Σc1 : ∀ {R : Set} (s : List (Event√ R)) → #e s ≡ Σc 𝟙 (labels s)
#e≡Σc1 []          = refl
#e≡Σc1 (evl _ ∷ s) = cong suc (#e≡Σc1 s)
#e≡Σc1 (√ _ ∷ s)   = #e≡Σc1 s

-- scaling a weight scales its sum
Σc-* : ∀ a (c : Event → ℕ) ls → Σc (λ e → a * c e) ls ≡ a * Σc c ls
Σc-* a c []       = sym (*-zeroʳ′ a)
  where
    -- times zero
    *-zeroʳ′ : ∀ n → n * 0 ≡ 0
    *-zeroʳ′ zero    = refl
    *-zeroʳ′ (suc n) = *-zeroʳ′ n
Σc-* a c (e ∷ ls) = trans (cong (a * c e +_) (Σc-* a c ls)) (sym (*-distribˡ-+ a (c e) (Σc c ls)))

-- a weight at most 1 on every label weighs at most the unit weight
Σ≤1 : ∀ {c : Event → ℕ} ls → (∀ e → T (c e ≤ᵇ 1)) → Σc c ls ≤ Σc 𝟙 ls
Σ≤1 ls f = Σc-≤ (allL (λ e → ≤ᵇ⇒≤ _ _ (f e)) ls)

-- a step into a right-nested sum
in+ : ∀ {x y} z → x ≤ y → x ≤ z + y
in+ {y = y} z h = ≤-trans h (m≤n+m y z)

-- a label fact meets a composite event
AllL-AnyE : ∀ {R : Set} {P Q : Event → Set} {Z : Set} (s : List (Event√ R)) → AllL P (labels s) → AnyE Q s
          → (∀ {e} → P e → Q e → Z) → Z
AllL-AnyE (evl e ∷ s) (p ∷ ps) (here q)  f = f p q
AllL-AnyE (evl e ∷ s) (p ∷ ps) (there a) f = AllL-AnyE s ps a f
AllL-AnyE (√ _ ∷ s)   ps        (here ())
AllL-AnyE (√ _ ∷ s)   ps        (there a) f = AllL-AnyE s ps a f

------------------------------------------------------------------------
-- the threads
------------------------------------------------------------------------

-- the five stores
ST : Node → Proc
ST n = blockStoreL n [] ⦀ (ebStore n [] ⦀ (bodyStore n [] ⦀ (mempool n [] ⦀ voteStore n ([] , []))))

-- the read bounds the stores give a run
RH : ℕ → List (Event√ (UP.⊤ {0ℓ})) → Set₁
RH B s = (∀ j → AnyE (IsGetAt j) s → j < B) × ((∀ j → AnyE (IsGetVoteAt j) s → j < length U) × (∀ j → AnyE (IsGetTxAt j) s → j < 2))

-- every run whose reads are below the bounds costs at most its credit plus `k`
RlH : ℕ → (Event → ℕ) → (Event → ℕ) → ℕ → Proc → Set₁
RlH B c d k P = ∀ {s W} → P ⟹⟨ s ⟩ W → RH B s → Σc c (labels s) ≤ Σc d (labels s) + k

-- interleaving adds the slacks (the read bounds pass to both sides)
rlH-⦀ : ∀ {B c d k₁ k₂} {P Q : Proc} → RlH B c d k₁ P → RlH B c d k₂ Q → RlH B c d (k₁ + k₂) (P ⦀ Q)
rlH-⦀ {B} {c} {d} {k₁} {k₂} {P} {Q} p q tr (r₁ , r₂ , r₃) with Par-trace-elim _ _ P Q tr
... | sP , sQ , _ , _ , tP , tQ , pi =
  subst₂ (λ x y → x ≤ y + (k₁ + k₂)) (sym (Σc-⦀ c pi)) (sym (Σc-⦀ d pi))
    (≤-trans (+-mono-≤ (p tP ((λ j a → r₁ j (AnyE-parL pi a)) , (λ j a → r₂ j (AnyE-parL pi a)) , (λ j a → r₃ j (AnyE-parL pi a))))
                       (q tQ ((λ j a → r₁ j (AnyE-parR pi a)) , (λ j a → r₂ j (AnyE-parR pi a)) , (λ j a → r₃ j (AnyE-parR pi a)))))
             (≤-≡ (+-inter (Σc d (labels sP)) k₁ (Σc d (labels sQ)) k₂)))

-- a weight below another bounds the same way
rlH-≤ : ∀ {B c c′ d k} {P : Proc} → (∀ e → c e ≤ c′ e) → RlH B c′ d k P → RlH B c d k P
rlH-≤ {P = P} f p {s} tr rh = ≤-trans (Σc-≤ (allL f (labels s))) (p tr rh)

-- ThreadAlpha's weight split: a group's masked weight is a summand of the forbidden weight
gmZ : ∀ g′ {o} e → IsZt (fw o e) → IsZt (gm o g′ e)
gmZ gCS  {o} e z = zl (gm o gCS e) (r2 z)
  where
    -- `IsZ` of a sum: its summands
    zl : ∀ a {b} → IsZt (a + b) → IsZt a
    zl zero    _ = _
    zl (suc a) ()
    -- … (right)
    zr : ∀ a {b} → IsZt (a + b) → IsZt b
    zr zero    z = z
    zr (suc a) ()
    -- past the wire weights
    r2 = λ (z : IsZt (fw o e)) → zr (cOut e) (zr (cIn e) z)
gmZ gAnn {o} e z = zl (gm o gAnn e) (zr (gm o gCS e) (zr (cOut e) (zr (cIn e) z)))
  where
    -- `IsZ` of a sum: its summands
    zl : ∀ a {b} → IsZt (a + b) → IsZt a
    zl zero    _ = _
    zl (suc a) ()
    -- … (right)
    zr : ∀ a {b} → IsZt (a + b) → IsZt b
    zr zero    z = z
    zr (suc a) ()
gmZ gOff {o} e z = zl (gm o gOff e) (zr (gm o gAnn e) (zr (gm o gCS e) (zr (cOut e) (zr (cIn e) z))))
  where
    -- `IsZ` of a sum: its summands
    zl : ∀ a {b} → IsZt (a + b) → IsZt a
    zl zero    _ = _
    zl (suc a) ()
    -- … (right)
    zr : ∀ a {b} → IsZt (a + b) → IsZt b
    zr zero    z = z
    zr (suc a) ()
gmZ gVot {o} e z = zl (gm o gVot e) (zr (gm o gOff e) (zr (gm o gAnn e) (zr (gm o gCS e) (zr (cOut e) (zr (cIn e) z)))))
  where
    -- `IsZ` of a sum: its summands
    zl : ∀ a {b} → IsZt (a + b) → IsZt a
    zl zero    _ = _
    zl (suc a) ()
    -- … (right)
    zr : ∀ a {b} → IsZt (a + b) → IsZt b
    zr zero    z = z
    zr (suc a) ()
gmZ gReq {o} e z = zl (gm o gReq e) (zr (gm o gVot e) (zr (gm o gOff e) (zr (gm o gAnn e) (zr (gm o gCS e) (zr (cOut e) (zr (cIn e) z))))))
  where
    -- `IsZ` of a sum: its summands
    zl : ∀ a {b} → IsZt (a + b) → IsZt a
    zl zero    _ = _
    zl (suc a) ()
    -- … (right)
    zr : ∀ a {b} → IsZt (a + b) → IsZt b
    zr zero    z = z
    zr (suc a) ()
gmZ gBTx {o} e z = zl (gm o gBTx e) (zr (gm o gReq e) (zr (gm o gVot e) (zr (gm o gOff e) (zr (gm o gAnn e) (zr (gm o gCS e)
                     (zr (cOut e) (zr (cIn e) z)))))))
  where
    -- `IsZ` of a sum: its summands
    zl : ∀ a {b} → IsZt (a + b) → IsZt a
    zl zero    _ = _
    zl (suc a) ()
    -- … (right)
    zr : ∀ a {b} → IsZt (a + b) → IsZt b
    zr zero    z = z
    zr (suc a) ()
gmZ gTS  {o} e z = zr (gm o gBTx e) (zr (gm o gReq e) (zr (gm o gVot e) (zr (gm o gOff e) (zr (gm o gAnn e) (zr (gm o gCS e)
                     (zr (cOut e) (zr (cIn e) z)))))))
  where
    -- `IsZ` of a sum: its right summand
    zr : ∀ a {b} → IsZt (a + b) → IsZt b
    zr zero    z = z
    zr (suc a) ()

-- a thread never emits a group it does not own
zt : ∀ g′ {o B d} {P : Proc} → (∀ {s W} → P ⟹⟨ s ⟩ W → AllL (Alw o) (labels s)) → RlH B (gm o g′) d 0 P
zt g′ {o} {B} {d} α {s} tr _ =
  subst (_≤ Σc d (labels s) + 0) (sym (Σc-0 (gm o g′) (AllL-map (λ {e} a → isZt≡ (gmZ g′ {o} e a)) (α tr)))) z≤n
  where
    -- … is zero
    isZt≡ : ∀ {k} → IsZt k → k ≡ 0
    isZt≡ {zero} _ = refl

-- … nor performs a wire input
zio : ∀ (w : WireW) {o B d} {P : Proc} → (∀ {s W} → P ⟹⟨ s ⟩ W → AllL (Alw o) (labels s)) → RlH B (wI w) d 0 P
zio w {o} {B} {d} α {s} tr _ =
  subst (_≤ Σc d (labels s) + 0) (sym (Σc-0 (wI w) (AllL-map (λ {e} a → Cls.oN (cls e) (isZt≡ (zl (cIn e) a)) w) (α tr)))) z≤n
  where
    -- … is zero
    isZt≡ : ∀ {k} → IsZt k → k ≡ 0
    isZt≡ {zero} _ = refl
    -- `IsZ` of a sum: its left summand
    zl : ∀ a {b} → IsZt (a + b) → IsZt a
    zl zero    _ = _
    zl (suc a) ()

-- the trigger weight of the threads' event count (the certificates first)
TWr : Event → ℕ
TWr e = 4 * cForge e + (2 * cSubmit e + (5 * rep gRF e + (5 * rep gLN e + (rep gBT e + (3 * rep gBQ e + (3 * rep gTQ e
      + 4 * rep grTS e))))))

-- … with the certificates
TW : Event → ℕ
TW e = cCert e + TWr e

-- a count with one trigger, read against a credit weight
cv1 : ∀ {R : Set} (s : List (Event√ R)) (a k : ℕ) (t : Event → ℕ) {D : Event → ℕ} → (∀ e → a * t e ≤ D e)
    → #e s ≤ a * Σc t (labels s) + k → #e s ≤ Σc D (labels s) + k
cv1 s a k t pw h =
  ≤-trans h (+-monoˡ-≤ k (≤-trans (≤-≡ (sym (Σc-* a t (labels s)))) (Σc-≤ (allL pw (labels s)))))

-- … with a list-length weight besides
cv2 : ∀ {R : Set} (s : List (Event√ R)) (a k : ℕ) (t u : Event → ℕ) {D : Event → ℕ} → (∀ e → a * t e + u e ≤ D e)
    → #e s ≤ a * Σc t (labels s) + k + Σc u (labels s) → #e s ≤ Σc D (labels s) + k
cv2 s a k t u pw h =
  ≤-trans h (≤-trans (≤-≡ (trans (+-assoc (a * Tt) k Uu) (trans (cong (a * Tt +_) (+-comm k Uu)) (sym (+-assoc (a * Tt) Uu k)))))
    (+-monoˡ-≤ k (≤-trans (≤-≡ (sym (trans (Σc-+ (λ e → a * t e) u (labels s)) (cong (_+ Uu) (Σc-* a t (labels s))))))
                           (Σc-≤ (allL pw (labels s))))))
  where
    -- the two totals
    Tt = Σc t (labels s)
    Uu = Σc u (labels s)

-- a count, as the unit weight
cnt : ∀ {R : Set} (s : List (Event√ R)) {D : Event → ℕ} {k} → #e s ≤ Σc D (labels s) + k → Σc 𝟙 (labels s) ≤ Σc D (labels s) + k
cnt s {D} {k} h = subst (_≤ Σc D (labels s) + k) (#e≡Σc1 s) h

-- a constant count
cvP : ∀ {R : Set} (s : List (Event√ R)) {D : Event → ℕ} k → #e s ≤ k → Σc 𝟙 (labels s) ≤ Σc D (labels s) + k
cvP s {D} k h = subst (_≤ Σc D (labels s) + k) (#e≡Σc1 s) (≤-trans h (m≤n+m k (Σc D (labels s))))

-- the Notify reports are the counts plus the vote lengths
lnId : ∀ e → repLNP e ≡ cLnRep e + ℓRep lnpRecvVotes e
lnId e = solve 5 (λ a b c d v → a :+ (b :+ (c :+ (d :+ v))) := (a :+ (b :+ (c :+ d))) :+ v) refl
           (cRep lnpRecvBlockAnnouncement e) (cRep lnpRecvBlockOffer e) (cRep lnpRecvBlockTxsOffer e)
           (cRep lnpRecvVotes e) (ℓRep lnpRecvVotes e)
  where open +-*-Solver

-- the LN client's round count against its reports
lnA : ∀ x y v r → 5 * x + (y + v) ≤ 5 * (x + v) + (y + r)
lnA x y v r = subst (5 * x + (y + v) ≤_) (solve 4 (λ x y v r → (con 5 :* x :+ (y :+ v)) :+ (con 4 :* v :+ r)
                                                      := con 5 :* (x :+ v) :+ (y :+ r)) refl x y v r)
                (m≤m+n (5 * x + (y + v)) (4 * v + r))
  where open +-*-Solver

-- a count and its list lengths, against a scaled sum
kA : ∀ k x y → suc k * x + y ≤ suc k * (x + y)
kA k x y = ≤-trans (+-monoʳ-≤ (suc k * x) (m≤m+n y (k * y))) (≤-≡ (sym (*-distribˡ-+ (suc k) x y)))

-- the LN client's counts against the trigger weight
pLN : ∀ e → 5 * cLnRep e + ℓLnRep e ≤ TW e
pLN e = in+ (cCert e) (in+ (4 * cForge e) (in+ (2 * cSubmit e) (in+ (5 * rep gRF e)
          (subst (λ z → 5 * cLnRep e + ℓLnRep e ≤ 5 * z + (repLFc e + (3 * rep gBQ e + (3 * rep gTQ e + 4 * rep grTS e)))) (sym (lnId e))
            (lnA (cLnRep e) (repLFc e) (ℓRep lnpRecvVotes e) (3 * rep gBQ e + (3 * rep gTQ e + 4 * rep grTS e)))))))

-- … and against the body-request credit
pLNb : ∀ e → 5 * cLnRep e + ℓLnRep e ≤ 5 * rep gLN e + rep gBT e
pLNb e = subst (λ z → 5 * cLnRep e + ℓLnRep e ≤ 5 * z + repLFc e) (sym (lnId e))
           (≤-trans (lnA (cLnRep e) (repLFc e) (ℓRep lnpRecvVotes e) 0) (≤-≡ (cong (λ z → 5 * (cLnRep e + ℓRep lnpRecvVotes e) + z) (+-identityʳ _))))

-- a closure-offer report is a Notify report
pTxO : ∀ e → cRep lnpRecvBlockTxsOffer e ≤ rep gLN e
pTxO e = in+ (cRep lnpRecvBlockAnnouncement e) (in+ (cRep lnpRecvBlockOffer e) (m≤m+n _ _))

-- the closure-entry commands are the tx-closure group's
p1x : ∀ {x} → 1 * x ≤ x
p1x {x} = ≤-≡ (+-identityʳ x)

-- one vote command per vote-offer round
voteOne : ∀ n l d {s W} → voteOfferLoop n (l , d) ⟹⟨ s ⟩ W → Σc (cCmd lnpSendVotes) (labels s) ≤ #e s
voteOne n l d {s} tr = subst (Σc (cCmd lnpSendVotes) (labels s) ≤_) (sym (#e≡Σc1 s)) (Σc-≤ (loopAll {P = λ e → cCmd lnpSendVotes e ≤ 𝟙 e}
  {body = voteOfferBody n l (opposite d)} (λ k → AllT-⟶ (getVoteAtEv n k) (λ _ → z≤n) (λ v →
    AllT-Output ⦃ iVs ⦄ (apiLP l (opposite d) lnpSendVotes) _ ≤-refl AllT-Ret)) 0 tr))

-- one tx-reply command per tx-serve round
txsOne : ∀ n l d {s W} → tsServe n (l , d) ⟹⟨ s ⟩ W → Σc (cCmd sendTSReplyTxs) (labels s) ≤ #e s
txsOne n l d {s} tr = subst (Σc (cCmd sendTSReplyTxs) (labels s) ≤_) (sym (#e≡Σc1 s)) (Σc-≤ (loopAll {P = λ e → cCmd sendTSReplyTxs e ≤ 𝟙 e}
  {body = tsServeBody n l d} (λ k → AllT-⟶ (apiTS l d recvTSRequestTxIds) (λ _ → z≤n) (λ _ →
    AllT-⟶ (getTxAtEv n k) (λ _ → z≤n) (λ t → AllT-Output ⦃ iHs ⦄ (apiTS l d sendTSReplyTxIds) _ z≤n
      (AllT-⟶ (apiTS l d recvTSRequestTxs) (λ _ → z≤n) (λ _ → AllT-Output ⦃ iTs ⦄ (apiTS l d sendTSReplyTxs) _ ≤-refl AllT-Ret)))))
  0 tr))

-- two bounds by the same count
twice : ∀ {a b x k : ℕ} → a ≤ x → b ≤ x → x ≤ k → a + b ≤ k + k
twice ha hb hk = +-mono-≤ (≤-trans ha hk) (≤-trans hb hk)

------------------------------------------------------------------------
-- THE THREAD LAYER, folded over `endpointsOf` (Stage L, L2)
------------------------------------------------------------------------

-- one slack per instance of a non-empty list (`slk k [] = k`, so a one-endpoint node keeps its constant)
slk : ∀ {A : Set} → ℕ → List A → ℕ
slk k []       = k
slk k (_ ∷ xs) = k + slk k xs

-- slacks add
slk-+ : ∀ {A : Set} a b (xs : List A) → slk a xs + slk b xs ≡ slk (a + b) xs
slk-+ a b []       = refl
slk-+ a b (_ ∷ xs) = trans (+-inter a (slk a xs) b (slk b xs)) (cong ((a + b) +_) (slk-+ a b xs))

-- slacks are monotone
slk-mono : ∀ {A : Set} {a b} (xs : List A) → a ≤ b → slk a xs ≤ slk b xs
slk-mono []       h = h
slk-mono (_ ∷ xs) h = +-mono-≤ h (slk-mono xs h)

-- a zero slack stays zero
slk-0 : ∀ {A : Set} (xs : List A) → slk 0 xs ≡ 0
slk-0 []       = refl
slk-0 (_ ∷ xs) = slk-0 xs

-- the endpoints of a node past its first
tl : Node → List (Link × Dir)
tl n = proj₂ (endpointsOf n)

-- interleaving over a non-empty list of instances adds one slack per instance
rlH-⦀⁺ : ∀ {A : Set} {B c d k} (f : A → Proc) → (∀ x → RlH B c d k (f x)) → ∀ x xs → RlH B c d (slk k xs) (⦀⁺ (f x) (map f xs))
rlH-⦀⁺ f h x []       = h x
rlH-⦀⁺ f h x (y ∷ ys) = rlH-⦀ (h x) (rlH-⦀⁺ f h y ys)

-- the five node-level threads and every endpoint's ten
THn : Node → Proc
THn n = forgeL n ⦀ (ebIndex n ⦀ (voter n ⦀ (submit n ⦀ (certSink n ⦀ allThreadsL n))))

-- the node logic over every endpoint
LGn : Node → Proc
LGn n = THn n ∥⇘ storeES ⇙ ST n

-- the ten threads of one endpoint, composed
thr10 : ∀ {B c d k₆ k₇ k₈ k₉ k₁₀ k₁₁ k₁₂ k₁₃ k₁₄ k₁₅} n e
      → RlH B c d k₆ (clientLoop n e) → RlH B c d k₇ (serverLoopL n e)
      → RlH B c d k₈ (lnClientLoopL n e) → RlH B c d k₉ (lnServerLoopL n e)
      → RlH B c d k₁₀ (bodyOfferLoop n e) → RlH B c d k₁₁ (voteOfferLoop n e)
      → RlH B c d k₁₂ (ebServeLoop n e) → RlH B c d k₁₃ (ebTxsServeLoop n e)
      → RlH B c d k₁₄ (tsPull n e) → RlH B c d k₁₅ (tsServe n e)
      → RlH B c d (k₆ + (k₇ + (k₈ + (k₉ + (k₁₀ + (k₁₁ + (k₁₂ + (k₁₃ + (k₁₄ + k₁₅))))))))) (endpointThreadsL n e)
thr10 n e a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ =
  rlH-⦀ a₆ (rlH-⦀ a₇ (rlH-⦀ a₈ (rlH-⦀ a₉ (rlH-⦀ a₁₀ (rlH-⦀ a₁₁ (rlH-⦀ a₁₂ (rlH-⦀ a₁₃ (rlH-⦀ a₁₄ a₁₅))))))))

-- the five node threads and every endpoint, composed
thrN : ∀ {B c d k₁ k₂ k₃ k₄ k₅ kE} n
     → RlH B c d k₁ (forgeL n) → RlH B c d k₂ (ebIndex n) → RlH B c d k₃ (voter n) → RlH B c d k₄ (submit n)
     → RlH B c d k₅ (certSink n) → (∀ e → RlH B c d kE (endpointThreadsL n e))
     → RlH B c d (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + slk kE (tl n)))))) (THn n)
thrN n a₁ a₂ a₃ a₄ a₅ aE =
  rlH-⦀ a₁ (rlH-⦀ a₂ (rlH-⦀ a₃ (rlH-⦀ a₄ (rlH-⦀ a₅ (rlH-⦀⁺ (endpointThreadsL n) aE (proj₁ (endpointsOf n)) (tl n))))))

-- the endpoint threads' constant
KTe : ℕ → ℕ
KTe B = 5 + ((8 * B + 8) + (5 + ((2 * B + 2) + ((5 * B + 5) + ((2 * length U + 2) + (3 + (3 + (4 + (5 * 2 + 5)))))))))

-- the node's threads' constant (one `KTe` per endpoint)
KTn : Node → ℕ → ℕ
KTn n B = 4 + ((2 * B + 2) + ((3 * B + 3) + (2 + (1 + slk (KTe B) (tl n)))))


module _ (n : Node) (B : ℕ) where

  -- one endpoint's event count
  epCount : ∀ e → RlH B 𝟙 TW (KTe B) (endpointThreadsL n e)
  epCount (l , d₀) = thr10 n (l , d₀)
    (λ {s} tr _ → cnt s (cv1 s 5 5 (cRep recvCSRollforward) (λ e → in+ (cCert e) (in+ (4 * cForge e) (in+ (2 * cSubmit e) (m≤m+n _ _))))
                    (clientLoop-count n l d₀ tr)))
    (λ {s} tr rh → cvP s (8 * B + 8) (serverLoopL-count n l d₀ B tr (proj₁ rh)))
    (λ {s} tr _ → cnt s (cv2 s 5 5 cLnRep ℓLnRep pLN (lnClientLoopL-count n l d₀ tr)))
    (λ {s} tr rh → cvP s (2 * B + 2) (lnServerLoopL-count n l d₀ B tr (proj₁ rh)))
    (λ {s} tr rh → cvP s (5 * B + 5) (bodyOfferLoop-count n l d₀ B tr (proj₁ rh)))
    (λ {s} tr rh → cvP s (2 * length U + 2) (voteOfferLoop-count n l d₀ (length U) tr (proj₁ (proj₂ rh))))
    (λ {s} tr _ → cnt s (cv1 s 3 3 (cRep lfpReqBlockRequest) (λ e → in+ (cCert e) (in+ (4 * cForge e) (in+ (2 * cSubmit e)
                    (in+ (5 * rep gRF e) (in+ (5 * rep gLN e) (in+ (rep gBT e) (m≤m+n _ _))))))) (ebServeLoop-count n l d₀ tr)))
    (λ {s} tr _ → cnt s (cv2 s 3 3 (cRep lfpReqBlockTxsRequest) (ℓRep lfpReqBlockTxsRequest)
                    (λ e → in+ (cCert e) (in+ (4 * cForge e) (in+ (2 * cSubmit e) (in+ (5 * rep gRF e) (in+ (5 * rep gLN e)
                      (in+ (rep gBT e) (in+ (3 * rep gBQ e) (≤-trans (kA 2 (cRep lfpReqBlockTxsRequest e) (ℓRep lfpReqBlockTxsRequest e)) (m≤m+n _ _))))))))) (ebTxsServeLoop-count n l d₀ tr)))
    (λ {s} tr _ → cnt s (cv2 s 4 4 (cRep recvTSReplyTxIds) (ℓRep recvTSReplyTxs)
                    (λ e → in+ (cCert e) (in+ (4 * cForge e) (in+ (2 * cSubmit e) (in+ (5 * rep gRF e) (in+ (5 * rep gLN e)
                      (in+ (rep gBT e) (in+ (3 * rep gBQ e) (in+ (3 * rep gTQ e) (kA 3 (cRep recvTSReplyTxIds e) (ℓRep recvTSReplyTxs e)))))))))) (tsPull-count n l d₀ tr)))
    (λ {s} tr rh → cvP s (5 * 2 + 5) (tsServe-count n l d₀ 2 tr (proj₂ (proj₂ rh))))

  -- THE THREADS' EVENT COUNT, over every endpoint
  thrCountN : RlH B 𝟙 TW (KTn n B) (THn n)
  thrCountN = thrN n
    (λ {s} tr _ → cnt s (cv1 s 4 4 cForge (λ e → in+ (cCert e) (m≤m+n _ _)) (forgeL-count n tr)))
    (λ {s} tr rh → cvP s (2 * B + 2) (ebIndex-count n B tr (proj₁ rh)))
    (λ {s} tr rh → cvP s (3 * B + 3) (voter-count n B tr (proj₁ rh)))
    (λ {s} tr _ → cnt s (cv1 s 2 2 cSubmit (λ e → in+ (cCert e) (in+ (4 * cForge e) (m≤m+n _ _))) (submit-count n tr)))
    (λ {s} tr _ → cnt s (cv1 s 1 1 cCert (λ e → ≤-trans p1x (m≤m+n _ _)) (certSink-count n tr)))
    epCount

  -- the node threads emit no group command (none owns one)
  nz : ∀ g′ {d} → (RlH B (gm nothing g′) d 0 (forgeL n) × RlH B (gm nothing g′) d 0 (ebIndex n))
                × (RlH B (gm nothing g′) d 0 (voter n) × (RlH B (gm nothing g′) d 0 (submit n) × RlH B (gm nothing g′) d 0 (certSink n)))
  nz g′ = (zt g′ {nothing} (forgeL-α n) , zt g′ {nothing} (ebIndex-α n)) , (zt g′ {nothing} (voter-α n) , (zt g′ {nothing} (submit-α n) , zt g′ {nothing} (certSink-α n)))

  -- the node threads, against an endpoint fact of one group
  nodeG : ∀ g′ {d k} → (∀ e → RlH B (gm nothing g′) d k (endpointThreadsL n e)) → RlH B (gm nothing g′) d (slk k (tl n)) (THn n)
  nodeG g′ {d} aE = let ((a₁ , a₂) , (a₃ , (a₄ , a₅))) = nz g′ {d} in thrN n a₁ a₂ a₃ a₄ a₅ aE

  -- the RollForward commands: one ChainSync server thread per endpoint
  thrCSN : RlH B (gw gCS) z0 (slk ((8 * B + 8) + 0) (tl n)) (THn n)
  thrCSN = nodeG gCS λ { (l , d₀) → thr10 n (l , d₀) (zt gCS {nothing} (clientLoop-α n l d₀))
    (λ {s} tr rh → ≤-trans (serverLoopL-cmd n l d₀ tr) (≤-trans (serverLoopL-count n l d₀ B tr (proj₁ rh)) (m≤n+m (8 * B + 8) (Σc z0 (labels s)))))
    (zt gCS {(just gReq)} (lnClientLoopL-α n l d₀)) (zt gCS {(just gAnn)} (lnServerLoopL-α n l d₀)) (zt gCS {(just gOff)} (bodyOfferLoop-α n l d₀))
    (zt gCS {(just gVot)} (voteOfferLoop-α n l d₀)) (zt gCS {nothing} (ebServeLoop-α n l d₀)) (zt gCS {(just gBTx)} (ebTxsServeLoop-α n l d₀))
    (zt gCS {nothing} (tsPull-α n l d₀)) (zt gCS {(just gTS)} (tsServe-α n l d₀)) }

  -- the node threads, against an endpoint fact of a weight below one group's
  nodeZ : ∀ g′ {c d k} → (∀ e → c e ≤ gm nothing g′ e) → (∀ e → RlH B c d k (endpointThreadsL n e))
        → RlH B c d (slk k (tl n)) (THn n)
  nodeZ g′ {c} {d} f aE = let ((a₁ , a₂) , (a₃ , (a₄ , a₅))) = nz g′ {d} in
    thrN n (rlH-≤ f a₁) (rlH-≤ f a₂) (rlH-≤ f a₃) (rlH-≤ f a₄) (rlH-≤ f a₅) aE

  -- the announcements: one LN announcer per endpoint
  thrAnnN : RlH B (gw gAnn) z0 (slk ((2 * B + 2) + 0) (tl n)) (THn n)
  thrAnnN = nodeG gAnn λ { (l , d₀) → thr10 n (l , d₀) (zt gAnn {nothing} (clientLoop-α n l d₀)) (zt gAnn {(just gCS)} (serverLoopL-α n l d₀))
    (zt gAnn {(just gReq)} (lnClientLoopL-α n l d₀))
    (λ {s} tr rh → ≤-trans (lnServerLoopL-cmd n l d₀ tr) (≤-trans (lnServerLoopL-count n l d₀ B tr (proj₁ rh)) (m≤n+m (2 * B + 2) (Σc z0 (labels s)))))
    (zt gAnn {(just gOff)} (bodyOfferLoop-α n l d₀)) (zt gAnn {(just gVot)} (voteOfferLoop-α n l d₀)) (zt gAnn {nothing} (ebServeLoop-α n l d₀))
    (zt gAnn {(just gBTx)} (ebTxsServeLoop-α n l d₀)) (zt gAnn {nothing} (tsPull-α n l d₀)) (zt gAnn {(just gTS)} (tsServe-α n l d₀)) }

  -- the body and closure offers: one body offerer per endpoint
  thrOffN : RlH B (gw gOff) z0 (slk (((5 * B + 5) + (5 * B + 5)) + 0) (tl n)) (THn n)
  thrOffN = nodeG gOff λ { (l , d₀) → thr10 n (l , d₀) (zt gOff {nothing} (clientLoop-α n l d₀)) (zt gOff {(just gCS)} (serverLoopL-α n l d₀))
    (zt gOff {(just gReq)} (lnClientLoopL-α n l d₀)) (zt gOff {(just gAnn)} (lnServerLoopL-α n l d₀))
    (λ {s} tr rh → ≤-trans (≤-≡ (Σc-+ (cCmd lnpSendBlockOffer) (cCmd lnpSendBlockTxsOffer) (labels s)))
                     (≤-trans (twice (proj₁ (bodyOfferLoop-cmd n l d₀ tr)) (proj₂ (bodyOfferLoop-cmd n l d₀ tr))
                                     (bodyOfferLoop-count n l d₀ B tr (proj₁ rh))) (m≤n+m _ (Σc z0 (labels s)))))
    (zt gOff {(just gVot)} (voteOfferLoop-α n l d₀)) (zt gOff {nothing} (ebServeLoop-α n l d₀))
    (zt gOff {(just gBTx)} (ebTxsServeLoop-α n l d₀)) (zt gOff {nothing} (tsPull-α n l d₀)) (zt gOff {(just gTS)} (tsServe-α n l d₀)) }

  -- the votes: one vote offerer per endpoint
  thrVotN : RlH B (gw gVot) z0 (slk (((2 * length U + 2) + (2 * length U + 2)) + 0) (tl n)) (THn n)
  thrVotN = nodeG gVot λ { (l , d₀) → thr10 n (l , d₀) (zt gVot {nothing} (clientLoop-α n l d₀)) (zt gVot {(just gCS)} (serverLoopL-α n l d₀))
    (zt gVot {(just gReq)} (lnClientLoopL-α n l d₀)) (zt gVot {(just gAnn)} (lnServerLoopL-α n l d₀)) (zt gVot {(just gOff)} (bodyOfferLoop-α n l d₀))
    (λ {s} tr rh → ≤-trans (≤-≡ (Σc-+ (cCmd lnpSendVotes) (ℓCmd lnpSendVotes) (labels s)))
                     (≤-trans (twice (voteOne n l d₀ tr) (≤-trans (voteOffer-emits n l d₀ tr) (voteOne n l d₀ tr))
                                     (voteOfferLoop-count n l d₀ (length U) tr (proj₁ (proj₂ rh)))) (m≤n+m _ (Σc z0 (labels s)))))
    (zt gVot {nothing} (ebServeLoop-α n l d₀))
    (zt gVot {(just gBTx)} (ebTxsServeLoop-α n l d₀)) (zt gVot {nothing} (tsPull-α n l d₀)) (zt gVot {(just gTS)} (tsServe-α n l d₀)) }

  -- the tx replies: one tx server per endpoint
  thrTSN : RlH B (gw gTS) z0 (slk (((5 * 2 + 5) + (5 * 2 + 5)) + 0) (tl n)) (THn n)
  thrTSN = nodeG gTS λ { (l , d₀) → thr10 n (l , d₀) (zt gTS {nothing} (clientLoop-α n l d₀)) (zt gTS {(just gCS)} (serverLoopL-α n l d₀))
    (zt gTS {(just gReq)} (lnClientLoopL-α n l d₀)) (zt gTS {(just gAnn)} (lnServerLoopL-α n l d₀)) (zt gTS {(just gOff)} (bodyOfferLoop-α n l d₀))
    (zt gTS {(just gVot)} (voteOfferLoop-α n l d₀)) (zt gTS {nothing} (ebServeLoop-α n l d₀)) (zt gTS {(just gBTx)} (ebTxsServeLoop-α n l d₀))
    (zt gTS {nothing} (tsPull-α n l d₀))
    (λ {s} tr rh → ≤-trans (≤-≡ (Σc-+ (cCmd sendTSReplyTxIds) (ℓCmd sendTSReplyTxs) (labels s)))
                     (≤-trans (twice (proj₂ (proj₂ (tsServe-emits n l d₀ tr))) (≤-trans (proj₁ (proj₂ (tsServe-emits n l d₀ tr))) (txsOne n l d₀ tr))
                                     (tsServe-count n l d₀ 2 tr (proj₂ (proj₂ rh)))) (m≤n+m _ (Σc z0 (labels s))))) }

  -- the closure requests: the LN clients', at most two per closure-offer report
  thrTQN : RlH B (cmd gTQ) (λ e → rep gLN e + rep gLN e) (slk 0 (tl n)) (THn n)
  thrTQN = nodeZ gReq tq λ { (l , d₀) → thr10 n (l , d₀) (rlH-≤ tq (zt gReq {nothing} (clientLoop-α n l d₀)))
    (rlH-≤ tq (zt gReq {(just gCS)} (serverLoopL-α n l d₀)))
    (λ {s} tr rh → ≤-trans (≤-≡ (Σc-+ (cCmd lfpSendBlockTxsRequest) (ℓCmd lfpSendBlockTxsRequest) (labels s)))
                     (≤-trans (+-mono-≤ (fetchTxs-req n l d₀ tr) (≤-trans (proj₁ (fetchTxs-emits n l d₀ tr)) (fetchTxs-req n l d₀ tr)))
                       (≤-trans (≤-≡ (sym (Σc-+ (cRep lnpRecvBlockTxsOffer) (cRep lnpRecvBlockTxsOffer) (labels s))))
                         (≤-trans (Σc-≤ (allL (λ e → +-mono-≤ (pTxO e) (pTxO e)) (labels s))) (m≤m+n _ 0)))))
    (rlH-≤ tq (zt gReq {(just gAnn)} (lnServerLoopL-α n l d₀))) (rlH-≤ tq (zt gReq {(just gOff)} (bodyOfferLoop-α n l d₀)))
    (rlH-≤ tq (zt gReq {(just gVot)} (voteOfferLoop-α n l d₀))) (rlH-≤ tq (zt gReq {nothing} (ebServeLoop-α n l d₀)))
    (rlH-≤ tq (zt gReq {(just gBTx)} (ebTxsServeLoop-α n l d₀))) (rlH-≤ tq (zt gReq {nothing} (tsPull-α n l d₀))) (rlH-≤ tq (zt gReq {(just gTS)} (tsServe-α n l d₀))) }
    where
      -- the closure requests are part of the request group
      tq : ∀ e → cmd gTQ e ≤ gw gReq e
      tq e = m≤n+m (cmd gTQ e) (cCmd lfpSendBlockRequest e)

  -- the body requests: the LN clients', at most their events
  thrBQN : RlH B (cmd gBQ) (λ e → 5 * rep gLN e + rep gBT e) (slk (5 + 0) (tl n)) (THn n)
  thrBQN = nodeZ gReq bq λ { (l , d₀) → thr10 n (l , d₀) (rlH-≤ bq (zt gReq {nothing} (clientLoop-α n l d₀)))
    (rlH-≤ bq (zt gReq {(just gCS)} (serverLoopL-α n l d₀)))
    (λ {s} tr rh → ≤-trans (proj₁ (proj₂ (fetchTxs-emits n l d₀ tr))) (cv2 s 5 5 cLnRep ℓLnRep pLNb (lnClientLoopL-count n l d₀ tr)))
    (rlH-≤ bq (zt gReq {(just gAnn)} (lnServerLoopL-α n l d₀))) (rlH-≤ bq (zt gReq {(just gOff)} (bodyOfferLoop-α n l d₀)))
    (rlH-≤ bq (zt gReq {(just gVot)} (voteOfferLoop-α n l d₀))) (rlH-≤ bq (zt gReq {nothing} (ebServeLoop-α n l d₀)))
    (rlH-≤ bq (zt gReq {(just gBTx)} (ebTxsServeLoop-α n l d₀))) (rlH-≤ bq (zt gReq {nothing} (tsPull-α n l d₀))) (rlH-≤ bq (zt gReq {(just gTS)} (tsServe-α n l d₀))) }
    where
      -- the body requests are part of the request group
      bq : ∀ e → cmd gBQ e ≤ gw gReq e
      bq e = m≤m+n (cCmd lfpSendBlockRequest e) (cmd gTQ e)

  -- the closure entries: the closure servers', at most the requested offsets
  thrBTN : RlH B (gw gBTx) (rep gTQ) (slk 0 (tl n)) (THn n)
  thrBTN = nodeG gBTx λ { (l , d₀) → thr10 n (l , d₀) (zt gBTx {nothing} (clientLoop-α n l d₀)) (zt gBTx {(just gCS)} (serverLoopL-α n l d₀))
    (zt gBTx {(just gReq)} (lnClientLoopL-α n l d₀)) (zt gBTx {(just gAnn)} (lnServerLoopL-α n l d₀)) (zt gBTx {(just gOff)} (bodyOfferLoop-α n l d₀))
    (zt gBTx {(just gVot)} (voteOfferLoop-α n l d₀)) (zt gBTx {nothing} (ebServeLoop-α n l d₀))
    (λ {s} tr rh → ≤-trans (serveTxs-emits n l d₀ tr) (≤-trans (Σc-≤ (allL (λ e → m≤n+m (ℓRep lfpReqBlockTxsRequest e) (cRep lfpReqBlockTxsRequest e)) (labels s))) (m≤m+n _ 0)))
    (zt gBTx {nothing} (tsPull-α n l d₀)) (zt gBTx {(just gTS)} (tsServe-α n l d₀)) }

  -- no wire input
  thrION : ∀ w → RlH B (wI w) z0 (slk 0 (tl n)) (THn n)
  thrION w = thrN n (zio w {nothing} (forgeL-α n)) (zio w {nothing} (ebIndex-α n)) (zio w {nothing} (voter-α n)) (zio w {nothing} (submit-α n))
    (zio w {nothing} (certSink-α n)) λ { (l , d₀) → thr10 n (l , d₀) (zio w {nothing} (clientLoop-α n l d₀)) (zio w {(just gCS)} (serverLoopL-α n l d₀))
    (zio w {(just gReq)} (lnClientLoopL-α n l d₀)) (zio w {(just gAnn)} (lnServerLoopL-α n l d₀)) (zio w {(just gOff)} (bodyOfferLoop-α n l d₀))
    (zio w {(just gVot)} (voteOfferLoop-α n l d₀)) (zio w {nothing} (ebServeLoop-α n l d₀)) (zio w {(just gBTx)} (ebTxsServeLoop-α n l d₀))
    (zio w {nothing} (tsPull-α n l d₀)) (zio w {(just gTS)} (tsServe-α n l d₀)) }

------------------------------------------------------------------------
-- the stores and the logic
------------------------------------------------------------------------

-- every read below its store's bound
RdOK : ℕ → Event → Set
RdOK B e = (∀ j → IsGetAt j e → j < B) × ((∀ j → IsGetVoteAt j e → j < length U) × (∀ j → IsGetTxAt j e → j < 2))

-- what the stores give, on their joint labels
record StOut (X : List Block) (ls : List Event) : Set₁ where
  field
    sRd   : AllL (RdOK (length X + Σc cF ls)) ls
    sCert : Σc cCert ls ≤ 3
    sAlph : AllL (InA storeES) ls

-- THE STORES: under the block rely, every read is below its bound; at most three certificates
storesF : ∀ n X {s W} → ST n ⟹⟨ s ⟩ W → AllL (InX X) (labels s) → StOut X (labels s)
storesF n X {s} tr rely with Par-trace-elim _ _ (blockStoreL n []) _ tr
... | s1 , r1 , _ , _ , t1 , u1 , p1 with Par-trace-elim _ _ (ebStore n []) _ u1
... | s2 , r2 , _ , _ , t2 , u2 , pP with Par-trace-elim _ _ (bodyStore n []) _ u2
... | s3 , r3 , _ , _ , t3 , u3 , p3 with Par-trace-elim _ _ (mempool n []) _ u3
... | s4 , s5 , _ , _ , t4 , t5 , p4 = record
  { sRd   = AllL-⦀ rbR (AllL-⦀ (AllL-map nr (ebV t2)) (AllL-⦀ (AllL-map nr (bdV t3)) (AllL-⦀ mpR vtR p4) p3) pP) p1
  ; sCert = ≤-trans (≤-≡ (trans (Σc-⦀ cCert p1) (cong₂ _+_ (z0c (AllL-map (λ z → proj₂ (proj₂ z)) rbT))
              (trans (Σc-⦀ cCert pP) (cong₂ _+_ (z0c (AllL-map (λ z → proj₂ (proj₂ (proj₂ z))) (ebV t2)))
              (trans (Σc-⦀ cCert p3) (cong₂ _+_ (z0c (AllL-map (λ z → proj₂ (proj₂ (proj₂ z))) (bdV t3)))
              (trans (Σc-⦀ cCert p4) (cong (_+ Σc cCert (labels s5)) (z0c (AllL-map (λ z → proj₂ (proj₂ z)) mpT)))))))))))
              (voteStore-certs n t5)
  ; sAlph = AllL-⦀ (blockStoreL-alph n [] t1) (AllL-⦀ (ebStore-alph n [] t2) (AllL-⦀ (bodyStore-alph n [] t3)
              (AllL-⦀ (mempool-alph n [] t4) (voteStore-alph n ([] , []) t5) p4) p3) pP) p1 }
  where
    -- the joint read bound
    Bs = length X + Σc cF (labels s)
    -- no read, no certificate
    NR : Event → Set
    NR e = (∀ j → IsGetAt j e → ⊥) × ((∀ j → IsGetVoteAt j e → ⊥) × ((∀ j → IsGetTxAt j e → ⊥) × IsZ (cCert e)))
    -- … read below anything
    nr : ∀ {e} → NR e → RdOK Bs e
    nr (a , b , c , _) = (λ j g → ⊥-elim (a j g)) , (λ j g → ⊥-elim (b j g)) , (λ j g → ⊥-elim (c j g))
    -- a zero certificate weight sums to zero
    z0c : ∀ {ls} → AllL (λ e → IsZ (cCert e)) ls → Σc cCert ls ≡ 0
    z0c a = Σc-0 cCert (AllL-map isZ≡ a)
    -- the EB-entry store
    ebV : ∀ {s′ W} → ebStore n [] ⟹⟨ s′ ⟩ W → AllL NR (labels s′)
    ebV = loopAll (λ es → eb-All n es (λ _ → (λ _ ()) , (λ _ ()) , (λ _ ()) , _) (λ _ _ → (λ _ ()) , (λ _ ()) , (λ _ ()) , _)) []
    -- the EB-body store
    bdV : ∀ {s′ W} → bodyStore n [] ⟹⟨ s′ ⟩ W → AllL NR (labels s′)
    bdV = loopAll (λ bs → body-All n bs (λ _ → (λ _ ()) , (λ _ ()) , (λ _ ()) , _) (λ _ _ → (λ _ ()) , (λ _ ()) , (λ _ ()) , _)) []
    -- the RB store: no vote or tx read, no certificate
    VTC : Event → Set
    VTC e = (∀ j → IsGetVoteAt j e → ⊥) × ((∀ j → IsGetTxAt j e → ⊥) × IsZ (cCert e))
    -- … one round
    rbV : ∀ held → AllT VTC (storeStepL n held)
    rbV held =
      AllT-□ (AllT-⟶ (forgeEv n) (λ _ → (λ _ ()) , (λ _ ()) , _) (λ _ → AllT-Ret))
        (AllT-□ (AllT-⟶ (putEv n) (λ _ → (λ _ ()) , (λ _ ()) , _) (λ _ → AllT-Ret))
          (AllT-□ (ohV held) (oiAll (getAtEv n) (reverse held) 0 held (λ _ _ _ → (λ _ ()) , (λ _ ()) , _))))
      where
        -- the hand-over menu
        ohV : ∀ bs → AllT VTC (offerHeld n held bs)
        ohV []       = AllT-Stop
        ohV (b ∷ bs) = AllT-□ (AllT-Output (getEv n) b ((λ _ ()) , (λ _ ()) , _) AllT-Ret) (ohV bs)
    -- … its run
    rbT : AllL VTC (labels s1)
    rbT = loopAll rbV [] t1
    -- … and its reads, from the block rely
    rbR : AllL (RdOK Bs) (labels s1)
    rbR = AllL-map (λ { (r , v , x , _) → (λ j g → ≤-trans (r j g) (+-monoʳ-≤ (length X) (Σc-parL cF p1))) ,
                                        (λ j g → ⊥-elim (v j g)) , (λ j g → ⊥-elim (x j g)) })
            (zipL (blockStore-reads-prov n X t1 (AllL-parL p1 rely)) rbT)
    -- the mempool: no RB or vote read, no certificate
    mpT : AllL (λ e → (∀ j → IsGetAt j e → ⊥) × ((∀ j → IsGetVoteAt j e → ⊥) × IsZ (cCert e))) (labels s4)
    mpT = loopAll (λ ts → mem-All n ts (λ _ → (λ _ ()) , (λ _ ()) , _) (λ _ → (λ _ ()) , (λ _ ()) , _)
                           (λ _ _ _ → (λ _ ()) , (λ _ ()) , _) (λ _ _ → (λ _ ()) , (λ _ ()) , _)) [] t4
    -- … its reads
    mpR : AllL (RdOK Bs) (labels s4)
    mpR = AllL-map (λ { ((a , b , _) , c) → (λ j g → ⊥-elim (a j g)) , (λ j g → ⊥-elim (b j g)) , c }) (zipL mpT (mempool-reads n t4))
    -- the vote store: no RB or tx read
    vtT : AllL (λ e → (∀ j → IsGetAt j e → ⊥) × (∀ j → IsGetTxAt j e → ⊥)) (labels s5)
    vtT = loopAll {body = voteStep n} (λ v → vote-All n (proj₁ v) (proj₂ v) (λ _ → (λ _ ()) , (λ _ ())) (λ _ → (λ _ ()) , (λ _ ()))
                                         (λ _ _ _ → (λ _ ()) , (λ _ ())) (λ _ _ → (λ _ ()) , (λ _ ()))) ([] , []) t5
    -- … its reads
    vtR : AllL (RdOK Bs) (labels s5)
    vtR = AllL-map (λ { ((a , c) , b) → (λ j g → ⊥-elim (a j g)) , b , (λ j g → ⊥-elim (c j g)) }) (zipL vtT (voteStore-reads n t5))

-- a relay group's command bound, from its owner threads (one owner per endpoint)
CBn : Node → Gr → ℕ → List Event → ℕ
CBn n gRF  B ls = slk (8 * B + 8) (tl n)
CBn n grTS B ls = slk 30 (tl n)
CBn n gLN  B ls = slk (12 * B + (4 * length U + 16)) (tl n)
CBn n gTQ  B ls = 2 * Σc (rep gLN) ls
CBn n gBT  B ls = Σc (rep gTQ) ls
CBn n gBQ  B ls = 5 * Σc (rep gLN) ls + Σc (rep gBT) ls + slk 5 (tl n)

-- what the logic gives, on its own labels
record LogicOutN (n : Node) (X : List Block) (ls : List Event) : Set where
  field
    lB  : ℕ
    lB≤ : lB ≤ length X + Σc cF ls
    lT  : ℕ
    lT≤ : lT ≤ Σc TWr ls + (3 + KTn n lB)
    lH  : Σc (χ HK) ls + Σc cApi ls ≤ 4 * lT
    lio : ∀ w → Σc (wI w) ls ≡ 0
    lC  : ∀ g → Σc (cmd g) ls ≤ 2 * CBn n g lB ls

-- THE LOGIC: threads against stores
logicFN : ∀ n X {s W} → LGn n ⟹⟨ s ⟩ W → AllL (InX X) (labels s) → LogicOutN n X (labels s)
logicFN n X {s} tr rely with Par-trace-elim storeES _ (THn n) (ST n) tr
... | sT , sS , _ , _ , tT , tS , pi = record
  { lB  = Bs
  ; lB≤ = +-monoʳ-≤ (length X) (Σc-parR cF pi)
  ; lT  = Σc 𝟙 (labels sT)
  ; lT≤ = ≤-trans (thrCountN n Bs tT rh)
            (≤-trans (≤-≡ (cong (_+ KTn n Bs) (Σc-+ cCert TWr (labels sT))))
              (≤-trans (+-monoˡ-≤ (KTn n Bs) (+-mono-≤ (≤-trans (≤-≡ certEq) (StOut.sCert so)) (Σc-parL TWr pi)))
                (≤-≡ (solve 3 (λ c w k → (c :+ w) :+ k := w :+ (c :+ k)) refl 3 (Σc TWr (labels s)) (KTn n Bs)))))
  ; lH  = ≤-trans (+-mono-≤ (dup χ′ (λ e → proj₂ (Cls.o1 (cls e)))) (dup cApi (λ e → proj₁ (Cls.o1 (cls e)))))
            (≤-≡ (solve 1 (λ x → (x :+ x) :+ (x :+ x) := con 4 :* x) refl (Σc 𝟙 (labels sT))))
  ; lio = λ w → n≤0⇒n≡0 (≤-trans (Σc-par (wI w) pi) (≤-trans (+-monoʳ-≤ _ (subR (wI w) (StOut.sAlph so) pi))
                   (≤-≡ (cong (λ z → z + z) (n≤0⇒n≡0 (≤-trans (thrION n Bs w tT rh) (≤-≡ (cong₂ _+_ (Σz (labels sT)) (slk-0 (tl n))))))))))
  ; lC  = λ g → ≤-trans (Σc-par (cmd g) pi) (≤-trans (+-monoʳ-≤ _ (subR (cmd g) (StOut.sAlph so) pi))
                   (+-mono-≤ (cbT g) (≤-trans (cbT g) (m≤m+n _ 0)))) }
  where
    open +-*-Solver
    -- the stores' facts
    so = storesF n X tS (AllL-parR pi rely)
    -- the read bound
    Bs = length X + Σc cF (labels sS)
    -- the threads' reads are the stores'
    rh : RH Bs sT
    rh = (λ j a → AllL-AnyE sS (StOut.sRd so) (AnyE-sync (λ e p → Cls.oR (cls e) (inj₁ p)) pi a) (λ r q → proj₁ r j q))
       , (λ j a → AllL-AnyE sS (StOut.sRd so) (AnyE-sync (λ e p → Cls.oR (cls e) (inj₂ (inj₁ p))) pi a) (λ r q → proj₁ (proj₂ r) j q))
       , (λ j a → AllL-AnyE sS (StOut.sRd so) (AnyE-sync (λ e p → Cls.oR (cls e) (inj₂ (inj₂ p))) pi a) (λ r q → proj₂ (proj₂ r) j q))
    -- the threads' certificates are the stores'
    certEq : Σc cCert (labels sT) ≡ Σc cCert (labels sS)
    certEq = let z = Σc-sync cCert (λ e m → Cls.oS (cls e) m) pi in trans (proj₁ z) (sym (proj₂ z))
    -- the H-indicator
    χ′ : Event → ℕ
    χ′ = χ HK
    -- a weight at most 1: the logic weighs at most twice the threads' events
    dup : ∀ (c : Event → ℕ) → (∀ e → T (c e ≤ᵇ 1)) → Σc c (labels s) ≤ Σc 𝟙 (labels sT) + Σc 𝟙 (labels sT)
    dup c f = ≤-trans (Σc-par c pi) (≤-trans (+-monoʳ-≤ _ (subR c (StOut.sAlph so) pi))
                (+-mono-≤ (Σ≤1 (labels sT) f) (Σ≤1 (labels sT) f)))
    -- a bound with a zero credit
    noS : ∀ {c : Event → ℕ} {k} → Σc c (labels sT) ≤ Σc z0 (labels sT) + k → Σc c (labels sT) ≤ k
    noS {k = k} h = ≤-trans h (≤-≡ (cong (_+ k) (Σz (labels sT))))
    -- … and a trailing zero
    s0 : ∀ a → slk (a + 0) (tl n) ≡ slk a (tl n)
    s0 a = cong (λ z → slk z (tl n)) (+-identityʳ a)
    -- every relay group's commands, against its owner's bound
    cbT : ∀ g → Σc (cmd g) (labels sT) ≤ CBn n g Bs (labels s)
    cbT gRF  = ≤-trans (noS (thrCSN n Bs tT rh)) (≤-≡ (s0 _))
    cbT grTS = noS (thrTSN n Bs tT rh)
    cbT gLN  =
      ≤-trans (≤-≡ (trans (Σc-cong (allL (λ e → solve 5 (λ a o t c v → ((a :+ o) :+ t) :+ (c :+ v) := a :+ ((o :+ t) :+ (c :+ v))) refl
                       (cCmd lnpSendBlockAnnouncement e) (cCmd lnpSendBlockOffer e) (cCmd lnpSendBlockTxsOffer e)
                       (cCmd lnpSendVotes e) (ℓCmd lnpSendVotes e)) (labels sT)))
                     (trans (Σc-+ (gw gAnn) _ (labels sT)) (cong (Σc (gw gAnn) (labels sT) +_) (Σc-+ (gw gOff) (gw gVot) (labels sT))))))
        (≤-trans (+-mono-≤ (noS (thrAnnN n Bs tT rh)) (+-mono-≤ (noS (thrOffN n Bs tT rh)) (noS (thrVotN n Bs tT rh))))
          (≤-trans (≤-≡ (trans (cong (slk ((2 * Bs + 2) + 0) (tl n) +_) (slk-+ (((5 * Bs + 5) + (5 * Bs + 5)) + 0) (((2 * length U + 2) + (2 * length U + 2)) + 0) (tl n)))
                                (slk-+ ((2 * Bs + 2) + 0) ((((5 * Bs + 5) + (5 * Bs + 5)) + 0) + (((2 * length U + 2) + (2 * length U + 2)) + 0)) (tl n))))
            (slk-mono (tl n) (≤-≡ (solve 2 (λ b u → ((con 2 :* b :+ con 2) :+ con 0) :+ ((((con 5 :* b :+ con 5) :+ (con 5 :* b :+ con 5)) :+ con 0)
                                                 :+ (((con 2 :* u :+ con 2) :+ (con 2 :* u :+ con 2)) :+ con 0))
                                               := con 12 :* b :+ (con 4 :* u :+ con 16)) refl Bs (length U))))))
    cbT gTQ  = ≤-trans (thrTQN n Bs tT rh)
                 (≤-trans (≤-≡ (trans (trans (cong (_ +_) (slk-0 (tl n))) (+-identityʳ _)) (Σc-+ (rep gLN) (rep gLN) (labels sT))))
                   (≤-trans (+-mono-≤ (Σc-parL (rep gLN) pi) (≤-trans (Σc-parL (rep gLN) pi) (m≤m+n _ 0))) ≤-refl))
    cbT gBT  = ≤-trans (thrBTN n Bs tT rh) (≤-trans (≤-≡ (trans (cong (_ +_) (slk-0 (tl n))) (+-identityʳ _))) (Σc-parL (rep gTQ) pi))
    cbT gBQ  = ≤-trans (thrBQN n Bs tT rh)
                 (≤-trans (≤-≡ (cong (_+ slk (5 + 0) (tl n)) (trans (Σc-+ (λ e → 5 * rep gLN e) (rep gBT) (labels sT))
                                                     (cong (_+ Σc (rep gBT) (labels sT)) (Σc-* 5 (rep gLN) (labels sT))))))
                   (+-mono-≤ (+-mono-≤ (*-monoʳ-≤ 5 (Σc-parL (rep gLN) pi)) (Σc-parL (rep gBT) pi)) (≤-≡ (s0 5))))

------------------------------------------------------------------------
-- THE NODE LAYER (moved from Stage C's `Bound2`, Stage L, L4): a node's
-- bundles over every endpoint against its logic, across `apiES`
------------------------------------------------------------------------

-- what a node gives, on its own labels
record NodeOut (n : Node) (X : List Block) (ls : List Event) : Set where
  field
    nB nT : ℕ
    nB≤ : nB ≤ length X + Σc cF ls
    nT≤ : nT ≤ Σc TWr ls + (3 + KTn n nB)
    nH  : Σc (χ HK) ls + Σc (wI one) ls ≤ 12 * nT + Σc (wO one) ls + slk 24 (tl n)
    nG  : ∀ g → Σc (rep g) ls + Σc (wI (ww g)) ls ≤ Σc (wO (ww g)) ls + 2 * CBn n g nB ls

-- a command bound grows with the labels
CB-mono : ∀ n g B {ls ls′} → (∀ c → Σc c ls ≤ Σc c ls′) → CBn n g B ls ≤ CBn n g B ls′
CB-mono n gRF  B m = ≤-refl
CB-mono n grTS B m = ≤-refl
CB-mono n gLN  B m = ≤-refl
CB-mono n gTQ  B m = *-monoʳ-≤ 2 (m (rep gLN))
CB-mono n gBT  B m = m (rep gTQ)
CB-mono n gBQ  B m = +-mono-≤ (+-mono-≤ (*-monoʳ-≤ 5 (m (rep gLN))) (m (rep gBT))) ≤-refl

-- one slack per instance of a non-empty list of bundles
rl-⦀⁺ : ∀ {A : Set} {c d k} (f : A → Proc) → (∀ x → Rl c d k (f x)) → ∀ x xs → Rl c d (slk k xs) (⦀⁺ (f x) (map f xs))
rl-⦀⁺ f h x []       = h x
rl-⦀⁺ f h x (y ∷ ys) = rl-⦀ (h x) (rl-⦀⁺ f h y ys)

-- every incident bundle of a node pays a group's reports and wire inputs
bundlesG : ∀ g n → Rl (gc g) (gd g) (slk 0 (tl n)) (linkBundlesWith nodeBundleP n)
bundlesG g n = rl-⦀⁺ (bundleAtWith nodeBundleP) (λ ld → bundleG g (proj₁ ld) (proj₂ ld) (opposite (proj₂ ld)))
                 (proj₁ (endpointsOf n)) (tl n)

-- every incident bundle of a node pays its H-labels and wire inputs with api labels
bundlesB : ∀ n → Rl (λ e → χ HK e + wI one e) (λ e → cApi e + (cApi e + (cApi e + wO one e))) (slk 24 (tl n))
                    (linkBundlesWith nodeBundleP n)
bundlesB n = rl-⦀⁺ (bundleAtWith nodeBundleP) (λ ld → bundleB (proj₁ ld) (proj₂ ld) (opposite (proj₂ ld)))
               (proj₁ (endpointsOf n)) (tl n)

-- the node's H-count arithmetic
nArith : ∀ {cs ws xb xl wb a ob o t k} → cs ≤ xb + xl → ws ≤ wb → xb + wb ≤ a + (a + (a + ob)) + k → ob ≤ o
       → xl + a ≤ 4 * t → cs + ws ≤ 12 * t + o + k
nArith {cs} {ws} {xb} {xl} {wb} {a} {ob} {o} {t} {k} h1 h2 h3 h4 h5 =
  ≤-trans (+-mono-≤ h1 h2) (≤-trans (≤-≡ (solve 3 (λ xb xl wb → (xb :+ xl) :+ wb := (xb :+ wb) :+ xl) refl xb xl wb))
    (≤-trans (+-monoˡ-≤ xl h3)
      (≤-trans (≤-trans (m≤m+n _ (2 * xl)) (≤-≡ (solve 4 (λ a ob xl k → ((a :+ (a :+ (a :+ ob))) :+ k :+ xl) :+ con 2 :* xl
                                                            := con 3 :* (xl :+ a) :+ ob :+ k) refl a ob xl k)))
        (≤-trans (+-monoˡ-≤ k (+-mono-≤ (*-monoʳ-≤ 3 h5) h4)) (≤-≡ (solve 3 (λ t o k → con 3 :* (con 4 :* t) :+ o :+ k
                                                                        := con 12 :* t :+ o :+ k) refl t o k))))))
  where open +-*-Solver

-- one node, its bundles and threads over every endpoint
nodeF′ : ∀ n X {s W} → nodeWith nodeBundleP n (nodeLogicL n st₀) ⟹⟨ s ⟩ W → AllL (InX X) (labels s) → NodeOut n X (labels s)
nodeF′ n X {s} tr rely with Par-trace-elim apiES _ (linkBundlesWith nodeBundleP n) (LGn n) tr
... | sB , sL , _ , _ , tB , tL , pi = record
  { nB  = LogicOutN.lB lg
  ; nT  = LogicOutN.lT lg
  ; nB≤ = ≤-trans (LogicOutN.lB≤ lg) (+-monoʳ-≤ (length X) (mono cF))
  ; nT≤ = ≤-trans (LogicOutN.lT≤ lg) (+-monoˡ-≤ _ (mono TWr))
  ; nH  = nArith {Σc (χ HK) (labels s)} {Σc (wI one) (labels s)} {Σc (χ HK) (labels sB)} {Σc (χ HK) (labels sL)}
                   {Σc (wI one) (labels sB)} {Σc cApi (labels sL)} {Σc (wO one) (labels sB)} {Σc (wO one) (labels s)}
                   {LogicOutN.lT lg} (Σc-par (χ HK) pi) (wI0 one) hB (Σc-parL (wO one) pi) (LogicOutN.lH lg)
  ; nG  = λ g → ≤-trans (+-mono-≤ (≤-≡ (syncS (rep g) (offRep g))) (wI0 (ww g)))
                  (≤-trans (≤-trans (≤-≡ (sym (Σc-+ (rep g) (wI (ww g)) (labels sB))))
                              (≤-trans (bundlesG g n tB)
                                (≤-≡ (trans (trans (cong (_ +_) (slk-0 (tl n))) (+-identityʳ _)) (Σc-+ (wO (ww g)) (cmd g) (labels sB))))))
                    (+-mono-≤ (Σc-parL (wO (ww g)) pi)
                      (≤-trans (≤-≡ (syncA (cmd g) (offCmd g)))
                        (≤-trans (LogicOutN.lC lg g) (*-monoʳ-≤ 2 (CB-mono n g _ mono)))))) }
  where
    -- the logic's facts
    lg = logicFN n X tL (AllL-parR pi rely)
    -- the logic weighs at most the node
    mono : ∀ c → Σc c (labels sL) ≤ Σc c (labels s)
    mono c = Σc-parR c pi
    -- an api weight: the bundle weighs what the logic weighs
    syncA : ∀ c → (∀ e → ¬ InA apiES e → c e ≡ 0) → Σc c (labels sB) ≡ Σc c (labels sL)
    syncA c f = trans (proj₁ (Σc-sync c f pi)) (sym (proj₂ (Σc-sync c f pi)))
    -- … and what the node weighs
    syncS : ∀ c → (∀ e → ¬ InA apiES e → c e ≡ 0) → Σc c (labels s) ≡ Σc c (labels sB)
    syncS c f = sym (proj₁ (Σc-sync c f pi))
    -- the bundle's base fact, its api labels read on the logic
    hB : Σc (χ HK) (labels sB) + Σc (wI one) (labels sB)
       ≤ Σc cApi (labels sL) + (Σc cApi (labels sL) + (Σc cApi (labels sL) + Σc (wO one) (labels sB))) + slk 24 (tl n)
    hB = ≤-trans (≤-≡ (sym (Σc-+ (χ HK) (wI one) (labels sB)))) (≤-trans (bundlesB n tB) (≤-≡ (cong (_+ slk 24 (tl n))
           (trans (Σc-+ cApi _ (labels sB)) (cong₂ _+_ a (trans (Σc-+ cApi _ (labels sB)) (cong₂ _+_ a
             (trans (Σc-+ cApi (wO one) (labels sB)) (cong₂ _+_ a refl)))))))))
      where
        -- the api labels
        a = syncA cApi offApi
    -- the node's wire inputs are the bundle's (the logic has none)
    wI0 : ∀ w → Σc (wI w) (labels s) ≤ Σc (wI w) (labels sB)
    wI0 w = ≤-trans (Σc-par (wI w) pi) (≤-≡ (trans (cong (Σc (wI w) (labels sB) +_) (LogicOutN.lio lg w)) (+-identityʳ _)))

-- THE NODE: either node (no case split: the fold covers every endpoint)
nodeF : ∀ n X {s W} → nodeWith nodeBundleP n (nodeLogicL n st₀) ⟹⟨ s ⟩ W → AllL (InX X) (labels s) → NodeOut n X (labels s)
nodeF = nodeF′

-- the trigger weight, summed
ΣTW : ∀ ls → Σc TWr ls ≡ 4 * Σc cForge ls + (2 * Σc cSubmit ls + (5 * Σc (rep gRF) ls + (5 * Σc (rep gLN) ls
                       + (Σc (rep gBT) ls + (3 * Σc (rep gBQ) ls + (3 * Σc (rep gTQ) ls + 4 * Σc (rep grTS) ls))))))
ΣTW ls = trans (Σc-+ _ _ ls) (cong₂ _+_ (Σc-* 4 cForge ls) (trans (Σc-+ _ _ ls) (cong₂ _+_ (Σc-* 2 cSubmit ls)
          (trans (Σc-+ _ _ ls) (cong₂ _+_ (Σc-* 5 (rep gRF) ls) (trans (Σc-+ _ _ ls) (cong₂ _+_ (Σc-* 5 (rep gLN) ls)
          (trans (Σc-+ _ _ ls) (cong₂ _+_ refl (trans (Σc-+ _ _ ls) (cong₂ _+_ (Σc-* 3 (rep gBQ) ls)
          (trans (Σc-+ _ _ ls) (cong₂ _+_ (Σc-* 3 (rep gTQ) ls) (Σc-* 4 (rep grTS) ls))))))))))))))
